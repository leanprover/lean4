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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "error while initializing arithmetic operators:\ninstance for `"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "` "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "\nis not definitionally equal to the expected one "};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6;
static const lean_string_object l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "\nwhen only reducible definitions and instances are reduced"};
static const lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8;
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
static uint64_t _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0(void){
_start:
{
uint8_t v___x_47_; uint64_t v___x_48_; 
v___x_47_ = 3;
v___x_48_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__1));
v___x_51_ = l_Lean_stringToMessageData(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__3));
v___x_54_ = l_Lean_stringToMessageData(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__5));
v___x_57_ = l_Lean_stringToMessageData(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__7));
v___x_60_ = l_Lean_stringToMessageData(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(lean_object* v_declName_61_, lean_object* v_inst_62_, lean_object* v_inst_x27_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; uint8_t v_foApprox_70_; uint8_t v_ctxApprox_71_; uint8_t v_quasiPatternApprox_72_; uint8_t v_constApprox_73_; uint8_t v_isDefEqStuckEx_74_; uint8_t v_unificationHints_75_; uint8_t v_proofIrrelevance_76_; uint8_t v_assignSyntheticOpaque_77_; uint8_t v_offsetCnstrs_78_; uint8_t v_etaStruct_79_; uint8_t v_univApprox_80_; uint8_t v_iota_81_; uint8_t v_beta_82_; uint8_t v_proj_83_; uint8_t v_zeta_84_; uint8_t v_zetaDelta_85_; uint8_t v_zetaUnused_86_; uint8_t v_zetaHave_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_146_; 
v___x_69_ = l_Lean_Meta_Context_config(v_a_64_);
v_foApprox_70_ = lean_ctor_get_uint8(v___x_69_, 0);
v_ctxApprox_71_ = lean_ctor_get_uint8(v___x_69_, 1);
v_quasiPatternApprox_72_ = lean_ctor_get_uint8(v___x_69_, 2);
v_constApprox_73_ = lean_ctor_get_uint8(v___x_69_, 3);
v_isDefEqStuckEx_74_ = lean_ctor_get_uint8(v___x_69_, 4);
v_unificationHints_75_ = lean_ctor_get_uint8(v___x_69_, 5);
v_proofIrrelevance_76_ = lean_ctor_get_uint8(v___x_69_, 6);
v_assignSyntheticOpaque_77_ = lean_ctor_get_uint8(v___x_69_, 7);
v_offsetCnstrs_78_ = lean_ctor_get_uint8(v___x_69_, 8);
v_etaStruct_79_ = lean_ctor_get_uint8(v___x_69_, 10);
v_univApprox_80_ = lean_ctor_get_uint8(v___x_69_, 11);
v_iota_81_ = lean_ctor_get_uint8(v___x_69_, 12);
v_beta_82_ = lean_ctor_get_uint8(v___x_69_, 13);
v_proj_83_ = lean_ctor_get_uint8(v___x_69_, 14);
v_zeta_84_ = lean_ctor_get_uint8(v___x_69_, 15);
v_zetaDelta_85_ = lean_ctor_get_uint8(v___x_69_, 16);
v_zetaUnused_86_ = lean_ctor_get_uint8(v___x_69_, 17);
v_zetaHave_87_ = lean_ctor_get_uint8(v___x_69_, 18);
v_isSharedCheck_146_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_146_ == 0)
{
v___x_89_ = v___x_69_;
v_isShared_90_ = v_isSharedCheck_146_;
goto v_resetjp_88_;
}
else
{
lean_dec(v___x_69_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_146_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint8_t v_trackZetaDelta_91_; lean_object* v_zetaDeltaSet_92_; lean_object* v_lctx_93_; lean_object* v_localInstances_94_; lean_object* v_defEqCtx_x3f_95_; lean_object* v_synthPendingDepth_96_; lean_object* v_canUnfold_x3f_97_; uint8_t v_univApprox_98_; uint8_t v_inTypeClassResolution_99_; uint8_t v_cacheInferType_100_; uint8_t v___x_101_; lean_object* v_config_103_; 
v_trackZetaDelta_91_ = lean_ctor_get_uint8(v_a_64_, sizeof(void*)*7);
v_zetaDeltaSet_92_ = lean_ctor_get(v_a_64_, 1);
v_lctx_93_ = lean_ctor_get(v_a_64_, 2);
v_localInstances_94_ = lean_ctor_get(v_a_64_, 3);
v_defEqCtx_x3f_95_ = lean_ctor_get(v_a_64_, 4);
v_synthPendingDepth_96_ = lean_ctor_get(v_a_64_, 5);
v_canUnfold_x3f_97_ = lean_ctor_get(v_a_64_, 6);
v_univApprox_98_ = lean_ctor_get_uint8(v_a_64_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_99_ = lean_ctor_get_uint8(v_a_64_, sizeof(void*)*7 + 2);
v_cacheInferType_100_ = lean_ctor_get_uint8(v_a_64_, sizeof(void*)*7 + 3);
v___x_101_ = 3;
if (v_isShared_90_ == 0)
{
v_config_103_ = v___x_89_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 0, v_foApprox_70_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 1, v_ctxApprox_71_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 2, v_quasiPatternApprox_72_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 3, v_constApprox_73_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 4, v_isDefEqStuckEx_74_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 5, v_unificationHints_75_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 6, v_proofIrrelevance_76_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 7, v_assignSyntheticOpaque_77_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 8, v_offsetCnstrs_78_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 10, v_etaStruct_79_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 11, v_univApprox_80_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 12, v_iota_81_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 13, v_beta_82_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 14, v_proj_83_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 15, v_zeta_84_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 16, v_zetaDelta_85_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 17, v_zetaUnused_86_);
lean_ctor_set_uint8(v_reuseFailAlloc_145_, 18, v_zetaHave_87_);
v_config_103_ = v_reuseFailAlloc_145_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
uint64_t v___x_104_; uint64_t v___x_105_; uint64_t v___x_106_; uint64_t v___x_107_; uint64_t v___x_108_; uint64_t v_key_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
lean_ctor_set_uint8(v_config_103_, 9, v___x_101_);
v___x_104_ = l_Lean_Meta_Context_configKey(v_a_64_);
v___x_105_ = 2ULL;
v___x_106_ = lean_uint64_shift_right(v___x_104_, v___x_105_);
v___x_107_ = lean_uint64_shift_left(v___x_106_, v___x_105_);
v___x_108_ = lean_uint64_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__0);
v_key_109_ = lean_uint64_lor(v___x_107_, v___x_108_);
v___x_110_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_110_, 0, v_config_103_);
lean_ctor_set_uint64(v___x_110_, sizeof(void*)*1, v_key_109_);
lean_inc(v_canUnfold_x3f_97_);
lean_inc(v_synthPendingDepth_96_);
lean_inc(v_defEqCtx_x3f_95_);
lean_inc_ref(v_localInstances_94_);
lean_inc_ref(v_lctx_93_);
lean_inc(v_zetaDeltaSet_92_);
v___x_111_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_zetaDeltaSet_92_);
lean_ctor_set(v___x_111_, 2, v_lctx_93_);
lean_ctor_set(v___x_111_, 3, v_localInstances_94_);
lean_ctor_set(v___x_111_, 4, v_defEqCtx_x3f_95_);
lean_ctor_set(v___x_111_, 5, v_synthPendingDepth_96_);
lean_ctor_set(v___x_111_, 6, v_canUnfold_x3f_97_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*7, v_trackZetaDelta_91_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*7 + 1, v_univApprox_98_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*7 + 2, v_inTypeClassResolution_99_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*7 + 3, v_cacheInferType_100_);
lean_inc_ref(v_inst_x27_63_);
lean_inc_ref(v_inst_62_);
v___x_112_ = l_Lean_Meta_isExprDefEq(v_inst_62_, v_inst_x27_63_, v___x_111_, v_a_65_, v_a_66_, v_a_67_);
lean_dec_ref(v___x_111_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_136_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_136_ == 0)
{
v___x_115_ = v___x_112_;
v_isShared_116_ = v_isSharedCheck_136_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_dec(v___x_112_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_136_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
uint8_t v___x_117_; 
v___x_117_ = lean_unbox(v_a_113_);
lean_dec(v_a_113_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
lean_del_object(v___x_115_);
v___x_118_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__2);
v___x_119_ = l_Lean_MessageData_ofName(v_declName_61_);
v___x_120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__4);
v___x_122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v___x_123_ = l_Lean_indentExpr(v_inst_62_);
v___x_124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_122_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
v___x_125_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__6);
v___x_126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_124_);
lean_ctor_set(v___x_126_, 1, v___x_125_);
v___x_127_ = l_Lean_indentExpr(v_inst_x27_63_);
v___x_128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_126_);
lean_ctor_set(v___x_128_, 1, v___x_127_);
v___x_129_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___closed__8);
v___x_130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_128_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v___x_130_, v_a_64_, v_a_65_, v_a_66_, v_a_67_);
return v___x_131_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_134_; 
lean_dec_ref(v_inst_x27_63_);
lean_dec_ref(v_inst_62_);
lean_dec(v_declName_61_);
v___x_132_ = lean_box(0);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 0, v___x_132_);
v___x_134_ = v___x_115_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec_ref(v_inst_x27_63_);
lean_dec_ref(v_inst_62_);
lean_dec(v_declName_61_);
v_a_137_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_112_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_112_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed(lean_object* v_declName_147_, lean_object* v_inst_148_, lean_object* v_inst_x27_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst(v_declName_147_, v_inst_148_, v_inst_x27_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
lean_dec(v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(lean_object* v_00_u03b1_156_, lean_object* v_msg_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___redArg(v_msg_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0___boxed(lean_object* v_00_u03b1_164_, lean_object* v_msg_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_throwError___at___00__private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst_spec__0(v_00_u03b1_164_, v_msg_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0(lean_object* v_inst_172_, lean_object* v_declName_173_, lean_object* v___x_174_, lean_object* v_type_175_, lean_object* v_inst_176_, lean_object* v_____r_177_){
_start:
{
lean_object* v_canonExpr_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v_canonExpr_178_ = lean_ctor_get(v_inst_172_, 0);
lean_inc(v_canonExpr_178_);
lean_dec_ref(v_inst_172_);
v___x_179_ = l_Lean_mkConst(v_declName_173_, v___x_174_);
v___x_180_ = l_Lean_mkAppB(v___x_179_, v_type_175_, v_inst_176_);
v___x_181_ = lean_apply_1(v_canonExpr_178_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1(lean_object* v_inst_182_, lean_object* v_declName_183_, lean_object* v___x_184_, lean_object* v_type_185_, lean_object* v_expectedInst_186_, lean_object* v_inst_187_, lean_object* v_toBind_188_, lean_object* v_inst_189_){
_start:
{
lean_object* v___f_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
lean_inc_ref(v_inst_189_);
lean_inc(v_declName_183_);
v___f_190_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_190_, 0, v_inst_182_);
lean_closure_set(v___f_190_, 1, v_declName_183_);
lean_closure_set(v___f_190_, 2, v___x_184_);
lean_closure_set(v___f_190_, 3, v_type_185_);
lean_closure_set(v___f_190_, 4, v_inst_189_);
v___x_191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_191_, 0, v_declName_183_);
lean_closure_set(v___x_191_, 1, v_inst_189_);
lean_closure_set(v___x_191_, 2, v_expectedInst_186_);
v___x_192_ = lean_apply_2(v_inst_187_, lean_box(0), v___x_191_);
v___x_193_ = lean_apply_4(v_toBind_188_, lean_box(0), lean_box(0), v___x_192_, v___f_190_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_type_198_, lean_object* v_u_199_, lean_object* v_instDeclName_200_, lean_object* v_declName_201_, lean_object* v_expectedInst_202_){
_start:
{
lean_object* v_toBind_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___f_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_toBind_203_ = lean_ctor_get(v_inst_196_, 1);
lean_inc_n(v_toBind_203_, 2);
v___x_204_ = lean_box(0);
v___x_205_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_205_, 0, v_u_199_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
lean_inc_ref(v_type_198_);
lean_inc_ref(v___x_205_);
lean_inc_ref(v_inst_197_);
v___f_206_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_206_, 0, v_inst_197_);
lean_closure_set(v___f_206_, 1, v_declName_201_);
lean_closure_set(v___f_206_, 2, v___x_205_);
lean_closure_set(v___f_206_, 3, v_type_198_);
lean_closure_set(v___f_206_, 4, v_expectedInst_202_);
lean_closure_set(v___f_206_, 5, v_inst_194_);
lean_closure_set(v___f_206_, 6, v_toBind_203_);
v___x_207_ = l_Lean_mkConst(v_instDeclName_200_, v___x_205_);
v___x_208_ = l_Lean_Expr_app___override(v___x_207_, v_type_198_);
v___x_209_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_196_, v_inst_195_, v_inst_197_, v___x_208_);
v___x_210_ = lean_apply_4(v_toBind_203_, lean_box(0), lean_box(0), v___x_209_, v___f_206_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn(lean_object* v_m_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_type_216_, lean_object* v_u_217_, lean_object* v_instDeclName_218_, lean_object* v_declName_219_, lean_object* v_expectedInst_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_212_, v_inst_213_, v_inst_214_, v_inst_215_, v_type_216_, v_u_217_, v_instDeclName_218_, v_declName_219_, v_expectedInst_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0(lean_object* v_inst_222_, lean_object* v_declName_223_, lean_object* v___x_224_, lean_object* v_type_225_, lean_object* v_inst_226_, lean_object* v_____r_227_){
_start:
{
lean_object* v_canonExpr_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v_canonExpr_228_ = lean_ctor_get(v_inst_222_, 0);
lean_inc(v_canonExpr_228_);
lean_dec_ref(v_inst_222_);
v___x_229_ = l_Lean_mkConst(v_declName_223_, v___x_224_);
lean_inc_ref_n(v_type_225_, 2);
v___x_230_ = l_Lean_mkApp4(v___x_229_, v_type_225_, v_type_225_, v_type_225_, v_inst_226_);
v___x_231_ = lean_apply_1(v_canonExpr_228_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1(lean_object* v_inst_232_, lean_object* v_declName_233_, lean_object* v___x_234_, lean_object* v_type_235_, lean_object* v_expectedInst_236_, lean_object* v_inst_237_, lean_object* v_toBind_238_, lean_object* v_inst_239_){
_start:
{
lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_inc_ref(v_inst_239_);
lean_inc(v_declName_233_);
v___f_240_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_240_, 0, v_inst_232_);
lean_closure_set(v___f_240_, 1, v_declName_233_);
lean_closure_set(v___f_240_, 2, v___x_234_);
lean_closure_set(v___f_240_, 3, v_type_235_);
lean_closure_set(v___f_240_, 4, v_inst_239_);
v___x_241_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_241_, 0, v_declName_233_);
lean_closure_set(v___x_241_, 1, v_inst_239_);
lean_closure_set(v___x_241_, 2, v_expectedInst_236_);
v___x_242_ = lean_apply_2(v_inst_237_, lean_box(0), v___x_241_);
v___x_243_ = lean_apply_4(v_toBind_238_, lean_box(0), lean_box(0), v___x_242_, v___f_240_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_type_248_, lean_object* v_u_249_, lean_object* v_instDeclName_250_, lean_object* v_declName_251_, lean_object* v_expectedInst_252_){
_start:
{
lean_object* v_toBind_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___f_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v_toBind_253_ = lean_ctor_get(v_inst_246_, 1);
lean_inc_n(v_toBind_253_, 2);
v___x_254_ = lean_box(0);
lean_inc_n(v_u_249_, 2);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v_u_249_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_256_, 0, v_u_249_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v_u_249_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
lean_inc_ref_n(v_type_248_, 3);
lean_inc_ref(v___x_257_);
lean_inc_ref(v_inst_247_);
v___f_258_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg___lam__1), 8, 7);
lean_closure_set(v___f_258_, 0, v_inst_247_);
lean_closure_set(v___f_258_, 1, v_declName_251_);
lean_closure_set(v___f_258_, 2, v___x_257_);
lean_closure_set(v___f_258_, 3, v_type_248_);
lean_closure_set(v___f_258_, 4, v_expectedInst_252_);
lean_closure_set(v___f_258_, 5, v_inst_244_);
lean_closure_set(v___f_258_, 6, v_toBind_253_);
v___x_259_ = l_Lean_mkConst(v_instDeclName_250_, v___x_257_);
v___x_260_ = l_Lean_mkApp3(v___x_259_, v_type_248_, v_type_248_, v_type_248_);
v___x_261_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_246_, v_inst_245_, v_inst_247_, v___x_260_);
v___x_262_ = lean_apply_4(v_toBind_253_, lean_box(0), lean_box(0), v___x_261_, v___f_258_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn(lean_object* v_m_263_, lean_object* v_inst_264_, lean_object* v_inst_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_type_268_, lean_object* v_u_269_, lean_object* v_instDeclName_270_, lean_object* v_declName_271_, lean_object* v_expectedInst_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_264_, v_inst_265_, v_inst_266_, v_inst_267_, v_type_268_, v_u_269_, v_instDeclName_270_, v_declName_271_, v_expectedInst_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0(lean_object* v_inst_274_, lean_object* v___x_275_, lean_object* v___x_276_, lean_object* v_type_277_, lean_object* v___x_278_, lean_object* v_inst_279_, lean_object* v_____r_280_){
_start:
{
lean_object* v_canonExpr_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v_canonExpr_281_ = lean_ctor_get(v_inst_274_, 0);
lean_inc(v_canonExpr_281_);
lean_dec_ref(v_inst_274_);
v___x_282_ = l_Lean_mkConst(v___x_275_, v___x_276_);
lean_inc_ref(v_type_277_);
v___x_283_ = l_Lean_mkApp4(v___x_282_, v_type_277_, v___x_278_, v_type_277_, v_inst_279_);
v___x_284_ = lean_apply_1(v_canonExpr_281_, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1(lean_object* v___x_295_, lean_object* v_type_296_, lean_object* v_semiringInst_297_, lean_object* v___x_298_, lean_object* v_inst_299_, lean_object* v___x_300_, lean_object* v___x_301_, lean_object* v_inst_302_, lean_object* v_toBind_303_, lean_object* v_inst_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v_inst_x27_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___f_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_305_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__4));
v___x_306_ = l_Lean_mkConst(v___x_305_, v___x_295_);
lean_inc_ref(v_type_296_);
v_inst_x27_307_ = l_Lean_mkAppB(v___x_306_, v_type_296_, v_semiringInst_297_);
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1___closed__5));
v___x_309_ = l_Lean_Name_mkStr2(v___x_298_, v___x_308_);
lean_inc_ref(v_inst_304_);
lean_inc(v___x_309_);
v___f_310_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__0), 7, 6);
lean_closure_set(v___f_310_, 0, v_inst_299_);
lean_closure_set(v___f_310_, 1, v___x_309_);
lean_closure_set(v___f_310_, 2, v___x_300_);
lean_closure_set(v___f_310_, 3, v_type_296_);
lean_closure_set(v___f_310_, 4, v___x_301_);
lean_closure_set(v___f_310_, 5, v_inst_304_);
v___x_311_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_311_, 0, v___x_309_);
lean_closure_set(v___x_311_, 1, v_inst_304_);
lean_closure_set(v___x_311_, 2, v_inst_x27_307_);
v___x_312_ = lean_apply_2(v_inst_302_, lean_box(0), v___x_311_);
v___x_313_ = lean_apply_4(v_toBind_303_, lean_box(0), lean_box(0), v___x_312_, v___f_310_);
return v___x_313_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(0u);
v___x_318_ = l_Lean_Level_ofNat(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_u_323_, lean_object* v_type_324_, lean_object* v_semiringInst_325_){
_start:
{
lean_object* v_toBind_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___f_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_toBind_326_ = lean_ctor_get(v_inst_321_, 1);
lean_inc_n(v_toBind_326_, 2);
v___x_327_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__0));
v___x_328_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__1));
v___x_329_ = lean_obj_once(&l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2, &l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2_once, _init_l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___closed__2);
v___x_330_ = lean_box(0);
lean_inc(v_u_323_);
v___x_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_331_, 0, v_u_323_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
lean_inc_ref(v___x_331_);
v___x_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_329_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_333_, 0, v_u_323_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
lean_inc_ref(v___x_333_);
v___x_334_ = l_Lean_mkConst(v___x_328_, v___x_333_);
v___x_335_ = l_Lean_Nat_mkType;
lean_inc_ref(v_inst_322_);
lean_inc_ref_n(v_type_324_, 2);
v___f_336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg___lam__1), 10, 9);
lean_closure_set(v___f_336_, 0, v___x_331_);
lean_closure_set(v___f_336_, 1, v_type_324_);
lean_closure_set(v___f_336_, 2, v_semiringInst_325_);
lean_closure_set(v___f_336_, 3, v___x_327_);
lean_closure_set(v___f_336_, 4, v_inst_322_);
lean_closure_set(v___f_336_, 5, v___x_333_);
lean_closure_set(v___f_336_, 6, v___x_335_);
lean_closure_set(v___f_336_, 7, v_inst_319_);
lean_closure_set(v___f_336_, 8, v_toBind_326_);
v___x_337_ = l_Lean_mkApp3(v___x_334_, v_type_324_, v___x_335_, v_type_324_);
v___x_338_ = l_Lean_Meta_Sym_Arith_MonadCanon_synthInstance___redArg(v_inst_321_, v_inst_320_, v_inst_322_, v___x_337_);
v___x_339_ = lean_apply_4(v_toBind_326_, lean_box(0), lean_box(0), v___x_338_, v___f_336_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn(lean_object* v_m_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_u_345_, lean_object* v_type_346_, lean_object* v_semiringInst_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_341_, v_inst_342_, v_inst_343_, v_inst_344_, v_u_345_, v_type_346_, v_semiringInst_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0(lean_object* v___x_349_, lean_object* v___x_350_, lean_object* v___x_351_, lean_object* v_type_352_, lean_object* v_canonExpr_353_, lean_object* v_inst_354_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_355_ = l_Lean_Name_mkStr2(v___x_349_, v___x_350_);
v___x_356_ = l_Lean_mkConst(v___x_355_, v___x_351_);
v___x_357_ = l_Lean_mkAppB(v___x_356_, v_type_352_, v_inst_354_);
v___x_358_ = lean_apply_1(v_canonExpr_353_, v___x_357_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1(lean_object* v___f_359_, lean_object* v_inst_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = lean_apply_1(v___f_359_, v_inst_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3(lean_object* v_toPure_362_, lean_object* v_val_363_, lean_object* v_toBind_364_, lean_object* v___f_365_, lean_object* v_____r_366_){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_apply_2(v_toPure_362_, lean_box(0), v_val_363_);
v___x_368_ = lean_apply_4(v_toBind_364_, lean_box(0), lean_box(0), v___x_367_, v___f_365_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2(lean_object* v_toPure_369_, lean_object* v_inst_x27_370_, lean_object* v_toBind_371_, lean_object* v___f_372_, lean_object* v___f_373_, lean_object* v___x_374_, lean_object* v___x_375_, lean_object* v_inst_376_, lean_object* v_____do__lift_377_){
_start:
{
if (lean_obj_tag(v_____do__lift_377_) == 0)
{
lean_object* v___x_378_; lean_object* v___x_379_; 
lean_dec(v_inst_376_);
lean_dec_ref(v___x_375_);
lean_dec_ref(v___x_374_);
lean_dec(v___f_373_);
v___x_378_ = lean_apply_2(v_toPure_369_, lean_box(0), v_inst_x27_370_);
v___x_379_ = lean_apply_4(v_toBind_371_, lean_box(0), lean_box(0), v___x_378_, v___f_372_);
return v___x_379_;
}
else
{
lean_object* v_val_380_; lean_object* v___f_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_dec(v___f_372_);
v_val_380_ = lean_ctor_get(v_____do__lift_377_, 0);
lean_inc_n(v_val_380_, 2);
lean_dec_ref(v_____do__lift_377_);
lean_inc(v_toBind_371_);
v___f_381_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_381_, 0, v_toPure_369_);
lean_closure_set(v___f_381_, 1, v_val_380_);
lean_closure_set(v___f_381_, 2, v_toBind_371_);
lean_closure_set(v___f_381_, 3, v___f_373_);
v___x_382_ = l_Lean_Name_mkStr2(v___x_374_, v___x_375_);
v___x_383_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_383_, 0, v___x_382_);
lean_closure_set(v___x_383_, 1, v_val_380_);
lean_closure_set(v___x_383_, 2, v_inst_x27_370_);
v___x_384_ = lean_apply_2(v_inst_376_, lean_box(0), v___x_383_);
v___x_385_ = lean_apply_4(v_toBind_371_, lean_box(0), lean_box(0), v___x_384_, v___f_381_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_u_398_, lean_object* v_type_399_, lean_object* v_semiringInst_400_){
_start:
{
lean_object* v_toApplicative_401_; lean_object* v_toBind_402_; lean_object* v_canonExpr_403_; lean_object* v_synthInstance_x3f_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_426_; 
v_toApplicative_401_ = lean_ctor_get(v_inst_396_, 0);
lean_inc_ref(v_toApplicative_401_);
v_toBind_402_ = lean_ctor_get(v_inst_396_, 1);
lean_inc(v_toBind_402_);
lean_dec_ref(v_inst_396_);
v_canonExpr_403_ = lean_ctor_get(v_inst_397_, 0);
v_synthInstance_x3f_404_ = lean_ctor_get(v_inst_397_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v_inst_397_);
if (v_isSharedCheck_426_ == 0)
{
v___x_406_ = v_inst_397_;
v_isShared_407_ = v_isSharedCheck_426_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_synthInstance_x3f_404_);
lean_inc(v_canonExpr_403_);
lean_dec(v_inst_397_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_426_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v_toPure_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v_toPure_408_ = lean_ctor_get(v_toApplicative_401_, 1);
lean_inc(v_toPure_408_);
lean_dec_ref(v_toApplicative_401_);
v___x_409_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__0));
v___x_410_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__1));
v___x_411_ = lean_box(0);
if (v_isShared_407_ == 0)
{
lean_ctor_set_tag(v___x_406_, 1);
lean_ctor_set(v___x_406_, 1, v___x_411_);
lean_ctor_set(v___x_406_, 0, v_u_398_);
v___x_413_ = v___x_406_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_u_398_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_411_);
v___x_413_ = v_reuseFailAlloc_425_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; lean_object* v_inst_x27_415_; lean_object* v___x_416_; lean_object* v___f_417_; lean_object* v___f_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v_instType_421_; lean_object* v___x_422_; lean_object* v___f_423_; lean_object* v___x_424_; 
lean_inc_ref_n(v___x_413_, 2);
v___x_414_ = l_Lean_mkConst(v___x_410_, v___x_413_);
lean_inc_ref_n(v_type_399_, 2);
v_inst_x27_415_ = l_Lean_mkAppB(v___x_414_, v_type_399_, v_semiringInst_400_);
v___x_416_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__2));
v___f_417_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__0), 6, 5);
lean_closure_set(v___f_417_, 0, v___x_416_);
lean_closure_set(v___f_417_, 1, v___x_409_);
lean_closure_set(v___f_417_, 2, v___x_413_);
lean_closure_set(v___f_417_, 3, v_type_399_);
lean_closure_set(v___f_417_, 4, v_canonExpr_403_);
v___f_418_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_418_, 0, v___f_417_);
v___x_419_ = ((lean_object*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___closed__3));
v___x_420_ = l_Lean_mkConst(v___x_419_, v___x_413_);
v_instType_421_ = l_Lean_Expr_app___override(v___x_420_, v_type_399_);
v___x_422_ = lean_apply_1(v_synthInstance_x3f_404_, v_instType_421_);
lean_inc_ref(v___f_418_);
lean_inc(v_toBind_402_);
v___f_423_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__2), 9, 8);
lean_closure_set(v___f_423_, 0, v_toPure_408_);
lean_closure_set(v___f_423_, 1, v_inst_x27_415_);
lean_closure_set(v___f_423_, 2, v_toBind_402_);
lean_closure_set(v___f_423_, 3, v___f_418_);
lean_closure_set(v___f_423_, 4, v___f_418_);
lean_closure_set(v___f_423_, 5, v___x_416_);
lean_closure_set(v___f_423_, 6, v___x_409_);
lean_closure_set(v___f_423_, 7, v_inst_395_);
v___x_424_ = lean_apply_4(v_toBind_402_, lean_box(0), lean_box(0), v___x_422_, v___f_423_);
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn(lean_object* v_m_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_u_431_, lean_object* v_type_432_, lean_object* v_semiringInst_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_428_, v_inst_429_, v_inst_430_, v_u_431_, v_type_432_, v_semiringInst_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0(lean_object* v_addFn_435_, lean_object* v_s_436_){
_start:
{
lean_object* v_id_437_; lean_object* v_type_438_; lean_object* v_u_439_; lean_object* v_ringInst_440_; lean_object* v_semiringInst_441_; lean_object* v_charInst_x3f_442_; lean_object* v_mulFn_x3f_443_; lean_object* v_subFn_x3f_444_; lean_object* v_negFn_x3f_445_; lean_object* v_powFn_x3f_446_; lean_object* v_intCastFn_x3f_447_; lean_object* v_natCastFn_x3f_448_; lean_object* v_one_x3f_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_457_; 
v_id_437_ = lean_ctor_get(v_s_436_, 0);
v_type_438_ = lean_ctor_get(v_s_436_, 1);
v_u_439_ = lean_ctor_get(v_s_436_, 2);
v_ringInst_440_ = lean_ctor_get(v_s_436_, 3);
v_semiringInst_441_ = lean_ctor_get(v_s_436_, 4);
v_charInst_x3f_442_ = lean_ctor_get(v_s_436_, 5);
v_mulFn_x3f_443_ = lean_ctor_get(v_s_436_, 7);
v_subFn_x3f_444_ = lean_ctor_get(v_s_436_, 8);
v_negFn_x3f_445_ = lean_ctor_get(v_s_436_, 9);
v_powFn_x3f_446_ = lean_ctor_get(v_s_436_, 10);
v_intCastFn_x3f_447_ = lean_ctor_get(v_s_436_, 11);
v_natCastFn_x3f_448_ = lean_ctor_get(v_s_436_, 12);
v_one_x3f_449_ = lean_ctor_get(v_s_436_, 13);
v_isSharedCheck_457_ = !lean_is_exclusive(v_s_436_);
if (v_isSharedCheck_457_ == 0)
{
lean_object* v_unused_458_; 
v_unused_458_ = lean_ctor_get(v_s_436_, 6);
lean_dec(v_unused_458_);
v___x_451_ = v_s_436_;
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_one_x3f_449_);
lean_inc(v_natCastFn_x3f_448_);
lean_inc(v_intCastFn_x3f_447_);
lean_inc(v_powFn_x3f_446_);
lean_inc(v_negFn_x3f_445_);
lean_inc(v_subFn_x3f_444_);
lean_inc(v_mulFn_x3f_443_);
lean_inc(v_charInst_x3f_442_);
lean_inc(v_semiringInst_441_);
lean_inc(v_ringInst_440_);
lean_inc(v_u_439_);
lean_inc(v_type_438_);
lean_inc(v_id_437_);
lean_dec(v_s_436_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_457_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v_addFn_435_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 6, v___x_453_);
v___x_455_ = v___x_451_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_id_437_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_type_438_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_u_439_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_ringInst_440_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_semiringInst_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 5, v_charInst_x3f_442_);
lean_ctor_set(v_reuseFailAlloc_456_, 6, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_456_, 7, v_mulFn_x3f_443_);
lean_ctor_set(v_reuseFailAlloc_456_, 8, v_subFn_x3f_444_);
lean_ctor_set(v_reuseFailAlloc_456_, 9, v_negFn_x3f_445_);
lean_ctor_set(v_reuseFailAlloc_456_, 10, v_powFn_x3f_446_);
lean_ctor_set(v_reuseFailAlloc_456_, 11, v_intCastFn_x3f_447_);
lean_ctor_set(v_reuseFailAlloc_456_, 12, v_natCastFn_x3f_448_);
lean_ctor_set(v_reuseFailAlloc_456_, 13, v_one_x3f_449_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1(lean_object* v_toPure_459_, lean_object* v_addFn_460_, lean_object* v_____r_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = lean_apply_2(v_toPure_459_, lean_box(0), v_addFn_460_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2(lean_object* v_toPure_463_, lean_object* v_modifyRing_464_, lean_object* v_toBind_465_, lean_object* v_addFn_466_){
_start:
{
lean_object* v___f_467_; lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_inc_ref(v_addFn_466_);
v___f_467_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_467_, 0, v_addFn_466_);
v___f_468_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_468_, 0, v_toPure_463_);
lean_closure_set(v___f_468_, 1, v_addFn_466_);
v___x_469_ = lean_apply_1(v_modifyRing_464_, v___f_467_);
v___x_470_ = lean_apply_4(v_toBind_465_, lean_box(0), lean_box(0), v___x_469_, v___f_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3(lean_object* v_toPure_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_toBind_492_, lean_object* v___f_493_, lean_object* v_ring_494_){
_start:
{
lean_object* v_addFn_x3f_495_; 
v_addFn_x3f_495_ = lean_ctor_get(v_ring_494_, 6);
if (lean_obj_tag(v_addFn_x3f_495_) == 1)
{
lean_object* v_val_496_; lean_object* v___x_497_; 
lean_inc_ref(v_addFn_x3f_495_);
lean_dec_ref(v_ring_494_);
lean_dec(v___f_493_);
lean_dec(v_toBind_492_);
lean_dec_ref(v_inst_491_);
lean_dec_ref(v_inst_490_);
lean_dec_ref(v_inst_489_);
lean_dec(v_inst_488_);
v_val_496_ = lean_ctor_get(v_addFn_x3f_495_, 0);
lean_inc(v_val_496_);
lean_dec_ref(v_addFn_x3f_495_);
v___x_497_ = lean_apply_2(v_toPure_487_, lean_box(0), v_val_496_);
return v___x_497_;
}
else
{
lean_object* v_type_498_; lean_object* v_u_499_; lean_object* v_semiringInst_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_expectedInst_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_toPure_487_);
v_type_498_ = lean_ctor_get(v_ring_494_, 1);
lean_inc_ref_n(v_type_498_, 3);
v_u_499_ = lean_ctor_get(v_ring_494_, 2);
lean_inc_n(v_u_499_, 2);
v_semiringInst_500_ = lean_ctor_get(v_ring_494_, 4);
lean_inc_ref(v_semiringInst_500_);
lean_dec_ref(v_ring_494_);
v___x_501_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_502_ = lean_box(0);
v___x_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_503_, 0, v_u_499_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
lean_inc_ref(v___x_503_);
v___x_504_ = l_Lean_mkConst(v___x_501_, v___x_503_);
v___x_505_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_506_ = l_Lean_mkConst(v___x_505_, v___x_503_);
v___x_507_ = l_Lean_mkAppB(v___x_506_, v_type_498_, v_semiringInst_500_);
v_expectedInst_508_ = l_Lean_mkAppB(v___x_504_, v_type_498_, v___x_507_);
v___x_509_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_510_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_511_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_488_, v_inst_489_, v_inst_490_, v_inst_491_, v_type_498_, v_u_499_, v___x_509_, v___x_510_, v_expectedInst_508_);
v___x_512_ = lean_apply_4(v_toBind_492_, lean_box(0), lean_box(0), v___x_511_, v___f_493_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn___redArg(lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_inst_517_){
_start:
{
lean_object* v_toApplicative_518_; lean_object* v_toBind_519_; lean_object* v_getRing_520_; lean_object* v_modifyRing_521_; lean_object* v_toPure_522_; lean_object* v___f_523_; lean_object* v___f_524_; lean_object* v___x_525_; 
v_toApplicative_518_ = lean_ctor_get(v_inst_515_, 0);
v_toBind_519_ = lean_ctor_get(v_inst_515_, 1);
lean_inc_n(v_toBind_519_, 3);
v_getRing_520_ = lean_ctor_get(v_inst_517_, 0);
lean_inc(v_getRing_520_);
v_modifyRing_521_ = lean_ctor_get(v_inst_517_, 1);
lean_inc(v_modifyRing_521_);
lean_dec_ref(v_inst_517_);
v_toPure_522_ = lean_ctor_get(v_toApplicative_518_, 1);
lean_inc_n(v_toPure_522_, 2);
v___f_523_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_523_, 0, v_toPure_522_);
lean_closure_set(v___f_523_, 1, v_modifyRing_521_);
lean_closure_set(v___f_523_, 2, v_toBind_519_);
v___f_524_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_524_, 0, v_toPure_522_);
lean_closure_set(v___f_524_, 1, v_inst_513_);
lean_closure_set(v___f_524_, 2, v_inst_514_);
lean_closure_set(v___f_524_, 3, v_inst_515_);
lean_closure_set(v___f_524_, 4, v_inst_516_);
lean_closure_set(v___f_524_, 5, v_toBind_519_);
lean_closure_set(v___f_524_, 6, v___f_523_);
v___x_525_ = lean_apply_4(v_toBind_519_, lean_box(0), lean_box(0), v_getRing_520_, v___f_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn(lean_object* v_m_526_, lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_inst_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Meta_Sym_Arith_getAddFn___redArg(v_inst_527_, v_inst_528_, v_inst_529_, v_inst_530_, v_inst_531_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0(lean_object* v_mulFn_533_, lean_object* v_s_534_){
_start:
{
lean_object* v_id_535_; lean_object* v_type_536_; lean_object* v_u_537_; lean_object* v_ringInst_538_; lean_object* v_semiringInst_539_; lean_object* v_charInst_x3f_540_; lean_object* v_addFn_x3f_541_; lean_object* v_subFn_x3f_542_; lean_object* v_negFn_x3f_543_; lean_object* v_powFn_x3f_544_; lean_object* v_intCastFn_x3f_545_; lean_object* v_natCastFn_x3f_546_; lean_object* v_one_x3f_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_id_535_ = lean_ctor_get(v_s_534_, 0);
v_type_536_ = lean_ctor_get(v_s_534_, 1);
v_u_537_ = lean_ctor_get(v_s_534_, 2);
v_ringInst_538_ = lean_ctor_get(v_s_534_, 3);
v_semiringInst_539_ = lean_ctor_get(v_s_534_, 4);
v_charInst_x3f_540_ = lean_ctor_get(v_s_534_, 5);
v_addFn_x3f_541_ = lean_ctor_get(v_s_534_, 6);
v_subFn_x3f_542_ = lean_ctor_get(v_s_534_, 8);
v_negFn_x3f_543_ = lean_ctor_get(v_s_534_, 9);
v_powFn_x3f_544_ = lean_ctor_get(v_s_534_, 10);
v_intCastFn_x3f_545_ = lean_ctor_get(v_s_534_, 11);
v_natCastFn_x3f_546_ = lean_ctor_get(v_s_534_, 12);
v_one_x3f_547_ = lean_ctor_get(v_s_534_, 13);
v_isSharedCheck_555_ = !lean_is_exclusive(v_s_534_);
if (v_isSharedCheck_555_ == 0)
{
lean_object* v_unused_556_; 
v_unused_556_ = lean_ctor_get(v_s_534_, 7);
lean_dec(v_unused_556_);
v___x_549_ = v_s_534_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_one_x3f_547_);
lean_inc(v_natCastFn_x3f_546_);
lean_inc(v_intCastFn_x3f_545_);
lean_inc(v_powFn_x3f_544_);
lean_inc(v_negFn_x3f_543_);
lean_inc(v_subFn_x3f_542_);
lean_inc(v_addFn_x3f_541_);
lean_inc(v_charInst_x3f_540_);
lean_inc(v_semiringInst_539_);
lean_inc(v_ringInst_538_);
lean_inc(v_u_537_);
lean_inc(v_type_536_);
lean_inc(v_id_535_);
lean_dec(v_s_534_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
v___x_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_551_, 0, v_mulFn_533_);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 7, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_id_535_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_type_536_);
lean_ctor_set(v_reuseFailAlloc_554_, 2, v_u_537_);
lean_ctor_set(v_reuseFailAlloc_554_, 3, v_ringInst_538_);
lean_ctor_set(v_reuseFailAlloc_554_, 4, v_semiringInst_539_);
lean_ctor_set(v_reuseFailAlloc_554_, 5, v_charInst_x3f_540_);
lean_ctor_set(v_reuseFailAlloc_554_, 6, v_addFn_x3f_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 7, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_554_, 8, v_subFn_x3f_542_);
lean_ctor_set(v_reuseFailAlloc_554_, 9, v_negFn_x3f_543_);
lean_ctor_set(v_reuseFailAlloc_554_, 10, v_powFn_x3f_544_);
lean_ctor_set(v_reuseFailAlloc_554_, 11, v_intCastFn_x3f_545_);
lean_ctor_set(v_reuseFailAlloc_554_, 12, v_natCastFn_x3f_546_);
lean_ctor_set(v_reuseFailAlloc_554_, 13, v_one_x3f_547_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1(lean_object* v_toPure_557_, lean_object* v_mulFn_558_, lean_object* v_____r_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_apply_2(v_toPure_557_, lean_box(0), v_mulFn_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2(lean_object* v_toPure_561_, lean_object* v_modifyRing_562_, lean_object* v_toBind_563_, lean_object* v_mulFn_564_){
_start:
{
lean_object* v___f_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_inc_ref(v_mulFn_564_);
v___f_565_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_565_, 0, v_mulFn_564_);
v___f_566_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_566_, 0, v_toPure_561_);
lean_closure_set(v___f_566_, 1, v_mulFn_564_);
v___x_567_ = lean_apply_1(v_modifyRing_562_, v___f_565_);
v___x_568_ = lean_apply_4(v_toBind_563_, lean_box(0), lean_box(0), v___x_567_, v___f_566_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3(lean_object* v_toPure_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_inst_588_, lean_object* v_inst_589_, lean_object* v_toBind_590_, lean_object* v___f_591_, lean_object* v_ring_592_){
_start:
{
lean_object* v_mulFn_x3f_593_; 
v_mulFn_x3f_593_ = lean_ctor_get(v_ring_592_, 7);
if (lean_obj_tag(v_mulFn_x3f_593_) == 1)
{
lean_object* v_val_594_; lean_object* v___x_595_; 
lean_inc_ref(v_mulFn_x3f_593_);
lean_dec_ref(v_ring_592_);
lean_dec(v___f_591_);
lean_dec(v_toBind_590_);
lean_dec_ref(v_inst_589_);
lean_dec_ref(v_inst_588_);
lean_dec_ref(v_inst_587_);
lean_dec(v_inst_586_);
v_val_594_ = lean_ctor_get(v_mulFn_x3f_593_, 0);
lean_inc(v_val_594_);
lean_dec_ref(v_mulFn_x3f_593_);
v___x_595_ = lean_apply_2(v_toPure_585_, lean_box(0), v_val_594_);
return v___x_595_;
}
else
{
lean_object* v_type_596_; lean_object* v_u_597_; lean_object* v_semiringInst_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_expectedInst_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec(v_toPure_585_);
v_type_596_ = lean_ctor_get(v_ring_592_, 1);
lean_inc_ref_n(v_type_596_, 3);
v_u_597_ = lean_ctor_get(v_ring_592_, 2);
lean_inc_n(v_u_597_, 2);
v_semiringInst_598_ = lean_ctor_get(v_ring_592_, 4);
lean_inc_ref(v_semiringInst_598_);
lean_dec_ref(v_ring_592_);
v___x_599_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_600_ = lean_box(0);
v___x_601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_601_, 0, v_u_597_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
lean_inc_ref(v___x_601_);
v___x_602_ = l_Lean_mkConst(v___x_599_, v___x_601_);
v___x_603_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_604_ = l_Lean_mkConst(v___x_603_, v___x_601_);
v___x_605_ = l_Lean_mkAppB(v___x_604_, v_type_596_, v_semiringInst_598_);
v_expectedInst_606_ = l_Lean_mkAppB(v___x_602_, v_type_596_, v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_608_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_609_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_586_, v_inst_587_, v_inst_588_, v_inst_589_, v_type_596_, v_u_597_, v___x_607_, v___x_608_, v_expectedInst_606_);
v___x_610_ = lean_apply_4(v_toBind_590_, lean_box(0), lean_box(0), v___x_609_, v___f_591_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn___redArg(lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_inst_615_){
_start:
{
lean_object* v_toApplicative_616_; lean_object* v_toBind_617_; lean_object* v_getRing_618_; lean_object* v_modifyRing_619_; lean_object* v_toPure_620_; lean_object* v___f_621_; lean_object* v___f_622_; lean_object* v___x_623_; 
v_toApplicative_616_ = lean_ctor_get(v_inst_613_, 0);
v_toBind_617_ = lean_ctor_get(v_inst_613_, 1);
lean_inc_n(v_toBind_617_, 3);
v_getRing_618_ = lean_ctor_get(v_inst_615_, 0);
lean_inc(v_getRing_618_);
v_modifyRing_619_ = lean_ctor_get(v_inst_615_, 1);
lean_inc(v_modifyRing_619_);
lean_dec_ref(v_inst_615_);
v_toPure_620_ = lean_ctor_get(v_toApplicative_616_, 1);
lean_inc_n(v_toPure_620_, 2);
v___f_621_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_621_, 0, v_toPure_620_);
lean_closure_set(v___f_621_, 1, v_modifyRing_619_);
lean_closure_set(v___f_621_, 2, v_toBind_617_);
v___f_622_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_622_, 0, v_toPure_620_);
lean_closure_set(v___f_622_, 1, v_inst_611_);
lean_closure_set(v___f_622_, 2, v_inst_612_);
lean_closure_set(v___f_622_, 3, v_inst_613_);
lean_closure_set(v___f_622_, 4, v_inst_614_);
lean_closure_set(v___f_622_, 5, v_toBind_617_);
lean_closure_set(v___f_622_, 6, v___f_621_);
v___x_623_ = lean_apply_4(v_toBind_617_, lean_box(0), lean_box(0), v_getRing_618_, v___f_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn(lean_object* v_m_624_, lean_object* v_inst_625_, lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_inst_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_Meta_Sym_Arith_getMulFn___redArg(v_inst_625_, v_inst_626_, v_inst_627_, v_inst_628_, v_inst_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0(lean_object* v_subFn_631_, lean_object* v_s_632_){
_start:
{
lean_object* v_id_633_; lean_object* v_type_634_; lean_object* v_u_635_; lean_object* v_ringInst_636_; lean_object* v_semiringInst_637_; lean_object* v_charInst_x3f_638_; lean_object* v_addFn_x3f_639_; lean_object* v_mulFn_x3f_640_; lean_object* v_negFn_x3f_641_; lean_object* v_powFn_x3f_642_; lean_object* v_intCastFn_x3f_643_; lean_object* v_natCastFn_x3f_644_; lean_object* v_one_x3f_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_653_; 
v_id_633_ = lean_ctor_get(v_s_632_, 0);
v_type_634_ = lean_ctor_get(v_s_632_, 1);
v_u_635_ = lean_ctor_get(v_s_632_, 2);
v_ringInst_636_ = lean_ctor_get(v_s_632_, 3);
v_semiringInst_637_ = lean_ctor_get(v_s_632_, 4);
v_charInst_x3f_638_ = lean_ctor_get(v_s_632_, 5);
v_addFn_x3f_639_ = lean_ctor_get(v_s_632_, 6);
v_mulFn_x3f_640_ = lean_ctor_get(v_s_632_, 7);
v_negFn_x3f_641_ = lean_ctor_get(v_s_632_, 9);
v_powFn_x3f_642_ = lean_ctor_get(v_s_632_, 10);
v_intCastFn_x3f_643_ = lean_ctor_get(v_s_632_, 11);
v_natCastFn_x3f_644_ = lean_ctor_get(v_s_632_, 12);
v_one_x3f_645_ = lean_ctor_get(v_s_632_, 13);
v_isSharedCheck_653_ = !lean_is_exclusive(v_s_632_);
if (v_isSharedCheck_653_ == 0)
{
lean_object* v_unused_654_; 
v_unused_654_ = lean_ctor_get(v_s_632_, 8);
lean_dec(v_unused_654_);
v___x_647_ = v_s_632_;
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_one_x3f_645_);
lean_inc(v_natCastFn_x3f_644_);
lean_inc(v_intCastFn_x3f_643_);
lean_inc(v_powFn_x3f_642_);
lean_inc(v_negFn_x3f_641_);
lean_inc(v_mulFn_x3f_640_);
lean_inc(v_addFn_x3f_639_);
lean_inc(v_charInst_x3f_638_);
lean_inc(v_semiringInst_637_);
lean_inc(v_ringInst_636_);
lean_inc(v_u_635_);
lean_inc(v_type_634_);
lean_inc(v_id_633_);
lean_dec(v_s_632_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_653_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_651_; 
v___x_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_649_, 0, v_subFn_631_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 8, v___x_649_);
v___x_651_ = v___x_647_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_id_633_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_type_634_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_u_635_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v_ringInst_636_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v_semiringInst_637_);
lean_ctor_set(v_reuseFailAlloc_652_, 5, v_charInst_x3f_638_);
lean_ctor_set(v_reuseFailAlloc_652_, 6, v_addFn_x3f_639_);
lean_ctor_set(v_reuseFailAlloc_652_, 7, v_mulFn_x3f_640_);
lean_ctor_set(v_reuseFailAlloc_652_, 8, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 9, v_negFn_x3f_641_);
lean_ctor_set(v_reuseFailAlloc_652_, 10, v_powFn_x3f_642_);
lean_ctor_set(v_reuseFailAlloc_652_, 11, v_intCastFn_x3f_643_);
lean_ctor_set(v_reuseFailAlloc_652_, 12, v_natCastFn_x3f_644_);
lean_ctor_set(v_reuseFailAlloc_652_, 13, v_one_x3f_645_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1(lean_object* v_toPure_655_, lean_object* v_subFn_656_, lean_object* v_____r_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = lean_apply_2(v_toPure_655_, lean_box(0), v_subFn_656_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2(lean_object* v_toPure_659_, lean_object* v_modifyRing_660_, lean_object* v_toBind_661_, lean_object* v_subFn_662_){
_start:
{
lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_inc_ref(v_subFn_662_);
v___f_663_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_663_, 0, v_subFn_662_);
v___f_664_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_664_, 0, v_toPure_659_);
lean_closure_set(v___f_664_, 1, v_subFn_662_);
v___x_665_ = lean_apply_1(v_modifyRing_660_, v___f_663_);
v___x_666_ = lean_apply_4(v_toBind_661_, lean_box(0), lean_box(0), v___x_665_, v___f_664_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3(lean_object* v_toPure_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_inst_687_, lean_object* v_inst_688_, lean_object* v_toBind_689_, lean_object* v___f_690_, lean_object* v_ring_691_){
_start:
{
lean_object* v_subFn_x3f_692_; 
v_subFn_x3f_692_ = lean_ctor_get(v_ring_691_, 8);
if (lean_obj_tag(v_subFn_x3f_692_) == 1)
{
lean_object* v_val_693_; lean_object* v___x_694_; 
lean_inc_ref(v_subFn_x3f_692_);
lean_dec_ref(v_ring_691_);
lean_dec(v___f_690_);
lean_dec(v_toBind_689_);
lean_dec_ref(v_inst_688_);
lean_dec_ref(v_inst_687_);
lean_dec_ref(v_inst_686_);
lean_dec(v_inst_685_);
v_val_693_ = lean_ctor_get(v_subFn_x3f_692_, 0);
lean_inc(v_val_693_);
lean_dec_ref(v_subFn_x3f_692_);
v___x_694_ = lean_apply_2(v_toPure_684_, lean_box(0), v_val_693_);
return v___x_694_;
}
else
{
lean_object* v_type_695_; lean_object* v_u_696_; lean_object* v_ringInst_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v_expectedInst_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v_toPure_684_);
v_type_695_ = lean_ctor_get(v_ring_691_, 1);
lean_inc_ref_n(v_type_695_, 3);
v_u_696_ = lean_ctor_get(v_ring_691_, 2);
lean_inc_n(v_u_696_, 2);
v_ringInst_697_ = lean_ctor_get(v_ring_691_, 3);
lean_inc_ref(v_ringInst_697_);
lean_dec_ref(v_ring_691_);
v___x_698_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__1));
v___x_699_ = lean_box(0);
v___x_700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_700_, 0, v_u_696_);
lean_ctor_set(v___x_700_, 1, v___x_699_);
lean_inc_ref(v___x_700_);
v___x_701_ = l_Lean_mkConst(v___x_698_, v___x_700_);
v___x_702_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__4));
v___x_703_ = l_Lean_mkConst(v___x_702_, v___x_700_);
v___x_704_ = l_Lean_mkAppB(v___x_703_, v_type_695_, v_ringInst_697_);
v_expectedInst_705_ = l_Lean_mkAppB(v___x_701_, v_type_695_, v___x_704_);
v___x_706_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__6));
v___x_707_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3___closed__8));
v___x_708_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_685_, v_inst_686_, v_inst_687_, v_inst_688_, v_type_695_, v_u_696_, v___x_706_, v___x_707_, v_expectedInst_705_);
v___x_709_ = lean_apply_4(v_toBind_689_, lean_box(0), lean_box(0), v___x_708_, v___f_690_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn___redArg(lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_inst_714_){
_start:
{
lean_object* v_toApplicative_715_; lean_object* v_toBind_716_; lean_object* v_getRing_717_; lean_object* v_modifyRing_718_; lean_object* v_toPure_719_; lean_object* v___f_720_; lean_object* v___f_721_; lean_object* v___x_722_; 
v_toApplicative_715_ = lean_ctor_get(v_inst_712_, 0);
v_toBind_716_ = lean_ctor_get(v_inst_712_, 1);
lean_inc_n(v_toBind_716_, 3);
v_getRing_717_ = lean_ctor_get(v_inst_714_, 0);
lean_inc(v_getRing_717_);
v_modifyRing_718_ = lean_ctor_get(v_inst_714_, 1);
lean_inc(v_modifyRing_718_);
lean_dec_ref(v_inst_714_);
v_toPure_719_ = lean_ctor_get(v_toApplicative_715_, 1);
lean_inc_n(v_toPure_719_, 2);
v___f_720_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_720_, 0, v_toPure_719_);
lean_closure_set(v___f_720_, 1, v_modifyRing_718_);
lean_closure_set(v___f_720_, 2, v_toBind_716_);
v___f_721_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getSubFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_721_, 0, v_toPure_719_);
lean_closure_set(v___f_721_, 1, v_inst_710_);
lean_closure_set(v___f_721_, 2, v_inst_711_);
lean_closure_set(v___f_721_, 3, v_inst_712_);
lean_closure_set(v___f_721_, 4, v_inst_713_);
lean_closure_set(v___f_721_, 5, v_toBind_716_);
lean_closure_set(v___f_721_, 6, v___f_720_);
v___x_722_ = lean_apply_4(v_toBind_716_, lean_box(0), lean_box(0), v_getRing_717_, v___f_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getSubFn(lean_object* v_m_723_, lean_object* v_inst_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_inst_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_Meta_Sym_Arith_getSubFn___redArg(v_inst_724_, v_inst_725_, v_inst_726_, v_inst_727_, v_inst_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0(lean_object* v_negFn_730_, lean_object* v_s_731_){
_start:
{
lean_object* v_id_732_; lean_object* v_type_733_; lean_object* v_u_734_; lean_object* v_ringInst_735_; lean_object* v_semiringInst_736_; lean_object* v_charInst_x3f_737_; lean_object* v_addFn_x3f_738_; lean_object* v_mulFn_x3f_739_; lean_object* v_subFn_x3f_740_; lean_object* v_powFn_x3f_741_; lean_object* v_intCastFn_x3f_742_; lean_object* v_natCastFn_x3f_743_; lean_object* v_one_x3f_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_id_732_ = lean_ctor_get(v_s_731_, 0);
v_type_733_ = lean_ctor_get(v_s_731_, 1);
v_u_734_ = lean_ctor_get(v_s_731_, 2);
v_ringInst_735_ = lean_ctor_get(v_s_731_, 3);
v_semiringInst_736_ = lean_ctor_get(v_s_731_, 4);
v_charInst_x3f_737_ = lean_ctor_get(v_s_731_, 5);
v_addFn_x3f_738_ = lean_ctor_get(v_s_731_, 6);
v_mulFn_x3f_739_ = lean_ctor_get(v_s_731_, 7);
v_subFn_x3f_740_ = lean_ctor_get(v_s_731_, 8);
v_powFn_x3f_741_ = lean_ctor_get(v_s_731_, 10);
v_intCastFn_x3f_742_ = lean_ctor_get(v_s_731_, 11);
v_natCastFn_x3f_743_ = lean_ctor_get(v_s_731_, 12);
v_one_x3f_744_ = lean_ctor_get(v_s_731_, 13);
v_isSharedCheck_752_ = !lean_is_exclusive(v_s_731_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_s_731_, 9);
lean_dec(v_unused_753_);
v___x_746_ = v_s_731_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_one_x3f_744_);
lean_inc(v_natCastFn_x3f_743_);
lean_inc(v_intCastFn_x3f_742_);
lean_inc(v_powFn_x3f_741_);
lean_inc(v_subFn_x3f_740_);
lean_inc(v_mulFn_x3f_739_);
lean_inc(v_addFn_x3f_738_);
lean_inc(v_charInst_x3f_737_);
lean_inc(v_semiringInst_736_);
lean_inc(v_ringInst_735_);
lean_inc(v_u_734_);
lean_inc(v_type_733_);
lean_inc(v_id_732_);
lean_dec(v_s_731_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v_negFn_730_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 9, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_id_732_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_type_733_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_u_734_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_ringInst_735_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_semiringInst_736_);
lean_ctor_set(v_reuseFailAlloc_751_, 5, v_charInst_x3f_737_);
lean_ctor_set(v_reuseFailAlloc_751_, 6, v_addFn_x3f_738_);
lean_ctor_set(v_reuseFailAlloc_751_, 7, v_mulFn_x3f_739_);
lean_ctor_set(v_reuseFailAlloc_751_, 8, v_subFn_x3f_740_);
lean_ctor_set(v_reuseFailAlloc_751_, 9, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_751_, 10, v_powFn_x3f_741_);
lean_ctor_set(v_reuseFailAlloc_751_, 11, v_intCastFn_x3f_742_);
lean_ctor_set(v_reuseFailAlloc_751_, 12, v_natCastFn_x3f_743_);
lean_ctor_set(v_reuseFailAlloc_751_, 13, v_one_x3f_744_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1(lean_object* v_toPure_754_, lean_object* v_negFn_755_, lean_object* v_____r_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = lean_apply_2(v_toPure_754_, lean_box(0), v_negFn_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2(lean_object* v_toPure_758_, lean_object* v_modifyRing_759_, lean_object* v_toBind_760_, lean_object* v_negFn_761_){
_start:
{
lean_object* v___f_762_; lean_object* v___f_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
lean_inc_ref(v_negFn_761_);
v___f_762_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_762_, 0, v_negFn_761_);
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_763_, 0, v_toPure_758_);
lean_closure_set(v___f_763_, 1, v_negFn_761_);
v___x_764_ = lean_apply_1(v_modifyRing_759_, v___f_762_);
v___x_765_ = lean_apply_4(v_toBind_760_, lean_box(0), lean_box(0), v___x_764_, v___f_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3(lean_object* v_toPure_779_, lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_toBind_784_, lean_object* v___f_785_, lean_object* v_ring_786_){
_start:
{
lean_object* v_negFn_x3f_787_; 
v_negFn_x3f_787_ = lean_ctor_get(v_ring_786_, 9);
if (lean_obj_tag(v_negFn_x3f_787_) == 1)
{
lean_object* v_val_788_; lean_object* v___x_789_; 
lean_inc_ref(v_negFn_x3f_787_);
lean_dec_ref(v_ring_786_);
lean_dec(v___f_785_);
lean_dec(v_toBind_784_);
lean_dec_ref(v_inst_783_);
lean_dec_ref(v_inst_782_);
lean_dec_ref(v_inst_781_);
lean_dec(v_inst_780_);
v_val_788_ = lean_ctor_get(v_negFn_x3f_787_, 0);
lean_inc(v_val_788_);
lean_dec_ref(v_negFn_x3f_787_);
v___x_789_ = lean_apply_2(v_toPure_779_, lean_box(0), v_val_788_);
return v___x_789_;
}
else
{
lean_object* v_type_790_; lean_object* v_u_791_; lean_object* v_ringInst_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_expectedInst_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v_toPure_779_);
v_type_790_ = lean_ctor_get(v_ring_786_, 1);
lean_inc_ref_n(v_type_790_, 2);
v_u_791_ = lean_ctor_get(v_ring_786_, 2);
lean_inc_n(v_u_791_, 2);
v_ringInst_792_ = lean_ctor_get(v_ring_786_, 3);
lean_inc_ref(v_ringInst_792_);
lean_dec_ref(v_ring_786_);
v___x_793_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__1));
v___x_794_ = lean_box(0);
v___x_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_795_, 0, v_u_791_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_Lean_mkConst(v___x_793_, v___x_795_);
v_expectedInst_797_ = l_Lean_mkAppB(v___x_796_, v_type_790_, v_ringInst_792_);
v___x_798_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__3));
v___x_799_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3___closed__5));
v___x_800_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_780_, v_inst_781_, v_inst_782_, v_inst_783_, v_type_790_, v_u_791_, v___x_798_, v___x_799_, v_expectedInst_797_);
v___x_801_ = lean_apply_4(v_toBind_784_, lean_box(0), lean_box(0), v___x_800_, v___f_785_);
return v___x_801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn___redArg(lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_inst_806_){
_start:
{
lean_object* v_toApplicative_807_; lean_object* v_toBind_808_; lean_object* v_getRing_809_; lean_object* v_modifyRing_810_; lean_object* v_toPure_811_; lean_object* v___f_812_; lean_object* v___f_813_; lean_object* v___x_814_; 
v_toApplicative_807_ = lean_ctor_get(v_inst_804_, 0);
v_toBind_808_ = lean_ctor_get(v_inst_804_, 1);
lean_inc_n(v_toBind_808_, 3);
v_getRing_809_ = lean_ctor_get(v_inst_806_, 0);
lean_inc(v_getRing_809_);
v_modifyRing_810_ = lean_ctor_get(v_inst_806_, 1);
lean_inc(v_modifyRing_810_);
lean_dec_ref(v_inst_806_);
v_toPure_811_ = lean_ctor_get(v_toApplicative_807_, 1);
lean_inc_n(v_toPure_811_, 2);
v___f_812_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_812_, 0, v_toPure_811_);
lean_closure_set(v___f_812_, 1, v_modifyRing_810_);
lean_closure_set(v___f_812_, 2, v_toBind_808_);
v___f_813_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNegFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_813_, 0, v_toPure_811_);
lean_closure_set(v___f_813_, 1, v_inst_802_);
lean_closure_set(v___f_813_, 2, v_inst_803_);
lean_closure_set(v___f_813_, 3, v_inst_804_);
lean_closure_set(v___f_813_, 4, v_inst_805_);
lean_closure_set(v___f_813_, 5, v_toBind_808_);
lean_closure_set(v___f_813_, 6, v___f_812_);
v___x_814_ = lean_apply_4(v_toBind_808_, lean_box(0), lean_box(0), v_getRing_809_, v___f_813_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNegFn(lean_object* v_m_815_, lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_inst_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_Sym_Arith_getNegFn___redArg(v_inst_816_, v_inst_817_, v_inst_818_, v_inst_819_, v_inst_820_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0(lean_object* v_powFn_822_, lean_object* v_s_823_){
_start:
{
lean_object* v_id_824_; lean_object* v_type_825_; lean_object* v_u_826_; lean_object* v_ringInst_827_; lean_object* v_semiringInst_828_; lean_object* v_charInst_x3f_829_; lean_object* v_addFn_x3f_830_; lean_object* v_mulFn_x3f_831_; lean_object* v_subFn_x3f_832_; lean_object* v_negFn_x3f_833_; lean_object* v_intCastFn_x3f_834_; lean_object* v_natCastFn_x3f_835_; lean_object* v_one_x3f_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_844_; 
v_id_824_ = lean_ctor_get(v_s_823_, 0);
v_type_825_ = lean_ctor_get(v_s_823_, 1);
v_u_826_ = lean_ctor_get(v_s_823_, 2);
v_ringInst_827_ = lean_ctor_get(v_s_823_, 3);
v_semiringInst_828_ = lean_ctor_get(v_s_823_, 4);
v_charInst_x3f_829_ = lean_ctor_get(v_s_823_, 5);
v_addFn_x3f_830_ = lean_ctor_get(v_s_823_, 6);
v_mulFn_x3f_831_ = lean_ctor_get(v_s_823_, 7);
v_subFn_x3f_832_ = lean_ctor_get(v_s_823_, 8);
v_negFn_x3f_833_ = lean_ctor_get(v_s_823_, 9);
v_intCastFn_x3f_834_ = lean_ctor_get(v_s_823_, 11);
v_natCastFn_x3f_835_ = lean_ctor_get(v_s_823_, 12);
v_one_x3f_836_ = lean_ctor_get(v_s_823_, 13);
v_isSharedCheck_844_ = !lean_is_exclusive(v_s_823_);
if (v_isSharedCheck_844_ == 0)
{
lean_object* v_unused_845_; 
v_unused_845_ = lean_ctor_get(v_s_823_, 10);
lean_dec(v_unused_845_);
v___x_838_ = v_s_823_;
v_isShared_839_ = v_isSharedCheck_844_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_one_x3f_836_);
lean_inc(v_natCastFn_x3f_835_);
lean_inc(v_intCastFn_x3f_834_);
lean_inc(v_negFn_x3f_833_);
lean_inc(v_subFn_x3f_832_);
lean_inc(v_mulFn_x3f_831_);
lean_inc(v_addFn_x3f_830_);
lean_inc(v_charInst_x3f_829_);
lean_inc(v_semiringInst_828_);
lean_inc(v_ringInst_827_);
lean_inc(v_u_826_);
lean_inc(v_type_825_);
lean_inc(v_id_824_);
lean_dec(v_s_823_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_844_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_840_; lean_object* v___x_842_; 
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v_powFn_822_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 10, v___x_840_);
v___x_842_ = v___x_838_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_id_824_);
lean_ctor_set(v_reuseFailAlloc_843_, 1, v_type_825_);
lean_ctor_set(v_reuseFailAlloc_843_, 2, v_u_826_);
lean_ctor_set(v_reuseFailAlloc_843_, 3, v_ringInst_827_);
lean_ctor_set(v_reuseFailAlloc_843_, 4, v_semiringInst_828_);
lean_ctor_set(v_reuseFailAlloc_843_, 5, v_charInst_x3f_829_);
lean_ctor_set(v_reuseFailAlloc_843_, 6, v_addFn_x3f_830_);
lean_ctor_set(v_reuseFailAlloc_843_, 7, v_mulFn_x3f_831_);
lean_ctor_set(v_reuseFailAlloc_843_, 8, v_subFn_x3f_832_);
lean_ctor_set(v_reuseFailAlloc_843_, 9, v_negFn_x3f_833_);
lean_ctor_set(v_reuseFailAlloc_843_, 10, v___x_840_);
lean_ctor_set(v_reuseFailAlloc_843_, 11, v_intCastFn_x3f_834_);
lean_ctor_set(v_reuseFailAlloc_843_, 12, v_natCastFn_x3f_835_);
lean_ctor_set(v_reuseFailAlloc_843_, 13, v_one_x3f_836_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1(lean_object* v_toPure_846_, lean_object* v_powFn_847_, lean_object* v_____r_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_apply_2(v_toPure_846_, lean_box(0), v_powFn_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2(lean_object* v_toPure_850_, lean_object* v_modifyRing_851_, lean_object* v_toBind_852_, lean_object* v_powFn_853_){
_start:
{
lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_inc_ref(v_powFn_853_);
v___f_854_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_854_, 0, v_powFn_853_);
v___f_855_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_855_, 0, v_toPure_850_);
lean_closure_set(v___f_855_, 1, v_powFn_853_);
v___x_856_ = lean_apply_1(v_modifyRing_851_, v___f_854_);
v___x_857_ = lean_apply_4(v_toBind_852_, lean_box(0), lean_box(0), v___x_856_, v___f_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3(lean_object* v_toPure_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_toBind_863_, lean_object* v___f_864_, lean_object* v_ring_865_){
_start:
{
lean_object* v_powFn_x3f_866_; 
v_powFn_x3f_866_ = lean_ctor_get(v_ring_865_, 10);
if (lean_obj_tag(v_powFn_x3f_866_) == 1)
{
lean_object* v_val_867_; lean_object* v___x_868_; 
lean_inc_ref(v_powFn_x3f_866_);
lean_dec_ref(v_ring_865_);
lean_dec(v___f_864_);
lean_dec(v_toBind_863_);
lean_dec_ref(v_inst_862_);
lean_dec_ref(v_inst_861_);
lean_dec_ref(v_inst_860_);
lean_dec(v_inst_859_);
v_val_867_ = lean_ctor_get(v_powFn_x3f_866_, 0);
lean_inc(v_val_867_);
lean_dec_ref(v_powFn_x3f_866_);
v___x_868_ = lean_apply_2(v_toPure_858_, lean_box(0), v_val_867_);
return v___x_868_;
}
else
{
lean_object* v_type_869_; lean_object* v_u_870_; lean_object* v_semiringInst_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v_toPure_858_);
v_type_869_ = lean_ctor_get(v_ring_865_, 1);
lean_inc_ref(v_type_869_);
v_u_870_ = lean_ctor_get(v_ring_865_, 2);
lean_inc(v_u_870_);
v_semiringInst_871_ = lean_ctor_get(v_ring_865_, 4);
lean_inc_ref(v_semiringInst_871_);
lean_dec_ref(v_ring_865_);
v___x_872_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_859_, v_inst_860_, v_inst_861_, v_inst_862_, v_u_870_, v_type_869_, v_semiringInst_871_);
v___x_873_ = lean_apply_4(v_toBind_863_, lean_box(0), lean_box(0), v___x_872_, v___f_864_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn___redArg(lean_object* v_inst_874_, lean_object* v_inst_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_inst_878_){
_start:
{
lean_object* v_toApplicative_879_; lean_object* v_toBind_880_; lean_object* v_getRing_881_; lean_object* v_modifyRing_882_; lean_object* v_toPure_883_; lean_object* v___f_884_; lean_object* v___f_885_; lean_object* v___x_886_; 
v_toApplicative_879_ = lean_ctor_get(v_inst_876_, 0);
v_toBind_880_ = lean_ctor_get(v_inst_876_, 1);
lean_inc_n(v_toBind_880_, 3);
v_getRing_881_ = lean_ctor_get(v_inst_878_, 0);
lean_inc(v_getRing_881_);
v_modifyRing_882_ = lean_ctor_get(v_inst_878_, 1);
lean_inc(v_modifyRing_882_);
lean_dec_ref(v_inst_878_);
v_toPure_883_ = lean_ctor_get(v_toApplicative_879_, 1);
lean_inc_n(v_toPure_883_, 2);
v___f_884_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_884_, 0, v_toPure_883_);
lean_closure_set(v___f_884_, 1, v_modifyRing_882_);
lean_closure_set(v___f_884_, 2, v_toBind_880_);
v___f_885_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_885_, 0, v_toPure_883_);
lean_closure_set(v___f_885_, 1, v_inst_874_);
lean_closure_set(v___f_885_, 2, v_inst_875_);
lean_closure_set(v___f_885_, 3, v_inst_876_);
lean_closure_set(v___f_885_, 4, v_inst_877_);
lean_closure_set(v___f_885_, 5, v_toBind_880_);
lean_closure_set(v___f_885_, 6, v___f_884_);
v___x_886_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v_getRing_881_, v___f_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn(lean_object* v_m_887_, lean_object* v_inst_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_inst_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = l_Lean_Meta_Sym_Arith_getPowFn___redArg(v_inst_888_, v_inst_889_, v_inst_890_, v_inst_891_, v_inst_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0(lean_object* v_intCastFn_894_, lean_object* v_s_895_){
_start:
{
lean_object* v_id_896_; lean_object* v_type_897_; lean_object* v_u_898_; lean_object* v_ringInst_899_; lean_object* v_semiringInst_900_; lean_object* v_charInst_x3f_901_; lean_object* v_addFn_x3f_902_; lean_object* v_mulFn_x3f_903_; lean_object* v_subFn_x3f_904_; lean_object* v_negFn_x3f_905_; lean_object* v_powFn_x3f_906_; lean_object* v_natCastFn_x3f_907_; lean_object* v_one_x3f_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_916_; 
v_id_896_ = lean_ctor_get(v_s_895_, 0);
v_type_897_ = lean_ctor_get(v_s_895_, 1);
v_u_898_ = lean_ctor_get(v_s_895_, 2);
v_ringInst_899_ = lean_ctor_get(v_s_895_, 3);
v_semiringInst_900_ = lean_ctor_get(v_s_895_, 4);
v_charInst_x3f_901_ = lean_ctor_get(v_s_895_, 5);
v_addFn_x3f_902_ = lean_ctor_get(v_s_895_, 6);
v_mulFn_x3f_903_ = lean_ctor_get(v_s_895_, 7);
v_subFn_x3f_904_ = lean_ctor_get(v_s_895_, 8);
v_negFn_x3f_905_ = lean_ctor_get(v_s_895_, 9);
v_powFn_x3f_906_ = lean_ctor_get(v_s_895_, 10);
v_natCastFn_x3f_907_ = lean_ctor_get(v_s_895_, 12);
v_one_x3f_908_ = lean_ctor_get(v_s_895_, 13);
v_isSharedCheck_916_ = !lean_is_exclusive(v_s_895_);
if (v_isSharedCheck_916_ == 0)
{
lean_object* v_unused_917_; 
v_unused_917_ = lean_ctor_get(v_s_895_, 11);
lean_dec(v_unused_917_);
v___x_910_ = v_s_895_;
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_one_x3f_908_);
lean_inc(v_natCastFn_x3f_907_);
lean_inc(v_powFn_x3f_906_);
lean_inc(v_negFn_x3f_905_);
lean_inc(v_subFn_x3f_904_);
lean_inc(v_mulFn_x3f_903_);
lean_inc(v_addFn_x3f_902_);
lean_inc(v_charInst_x3f_901_);
lean_inc(v_semiringInst_900_);
lean_inc(v_ringInst_899_);
lean_inc(v_u_898_);
lean_inc(v_type_897_);
lean_inc(v_id_896_);
lean_dec(v_s_895_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_916_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_912_; lean_object* v___x_914_; 
v___x_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_912_, 0, v_intCastFn_894_);
if (v_isShared_911_ == 0)
{
lean_ctor_set(v___x_910_, 11, v___x_912_);
v___x_914_ = v___x_910_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_id_896_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v_type_897_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_u_898_);
lean_ctor_set(v_reuseFailAlloc_915_, 3, v_ringInst_899_);
lean_ctor_set(v_reuseFailAlloc_915_, 4, v_semiringInst_900_);
lean_ctor_set(v_reuseFailAlloc_915_, 5, v_charInst_x3f_901_);
lean_ctor_set(v_reuseFailAlloc_915_, 6, v_addFn_x3f_902_);
lean_ctor_set(v_reuseFailAlloc_915_, 7, v_mulFn_x3f_903_);
lean_ctor_set(v_reuseFailAlloc_915_, 8, v_subFn_x3f_904_);
lean_ctor_set(v_reuseFailAlloc_915_, 9, v_negFn_x3f_905_);
lean_ctor_set(v_reuseFailAlloc_915_, 10, v_powFn_x3f_906_);
lean_ctor_set(v_reuseFailAlloc_915_, 11, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_915_, 12, v_natCastFn_x3f_907_);
lean_ctor_set(v_reuseFailAlloc_915_, 13, v_one_x3f_908_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1(lean_object* v_toPure_918_, lean_object* v_intCastFn_919_, lean_object* v_____r_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = lean_apply_2(v_toPure_918_, lean_box(0), v_intCastFn_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2(lean_object* v_toPure_922_, lean_object* v_modifyRing_923_, lean_object* v_toBind_924_, lean_object* v_intCastFn_925_){
_start:
{
lean_object* v___f_926_; lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
lean_inc_ref(v_intCastFn_925_);
v___f_926_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_926_, 0, v_intCastFn_925_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_927_, 0, v_toPure_922_);
lean_closure_set(v___f_927_, 1, v_intCastFn_925_);
v___x_928_ = lean_apply_1(v_modifyRing_923_, v___f_926_);
v___x_929_ = lean_apply_4(v_toBind_924_, lean_box(0), lean_box(0), v___x_928_, v___f_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3(lean_object* v___x_930_, lean_object* v___x_931_, lean_object* v___x_932_, lean_object* v_type_933_, lean_object* v_canonExpr_934_, lean_object* v_toBind_935_, lean_object* v___f_936_, lean_object* v_inst_937_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_938_ = l_Lean_Name_mkStr2(v___x_930_, v___x_931_);
v___x_939_ = l_Lean_mkConst(v___x_938_, v___x_932_);
v___x_940_ = l_Lean_mkAppB(v___x_939_, v_type_933_, v_inst_937_);
v___x_941_ = lean_apply_1(v_canonExpr_934_, v___x_940_);
v___x_942_ = lean_apply_4(v_toBind_935_, lean_box(0), lean_box(0), v___x_941_, v___f_936_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7(lean_object* v_toPure_948_, lean_object* v_inst_x27_949_, lean_object* v_toBind_950_, lean_object* v___f_951_, lean_object* v___f_952_, lean_object* v_inst_953_, lean_object* v_____do__lift_954_){
_start:
{
if (lean_obj_tag(v_____do__lift_954_) == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
lean_dec(v_inst_953_);
lean_dec(v___f_952_);
v___x_955_ = lean_apply_2(v_toPure_948_, lean_box(0), v_inst_x27_949_);
v___x_956_ = lean_apply_4(v_toBind_950_, lean_box(0), lean_box(0), v___x_955_, v___f_951_);
return v___x_956_;
}
else
{
lean_object* v_val_957_; lean_object* v___f_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec(v___f_951_);
v_val_957_ = lean_ctor_get(v_____do__lift_954_, 0);
lean_inc_n(v_val_957_, 2);
lean_dec_ref(v_____do__lift_954_);
lean_inc(v_toBind_950_);
v___f_958_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__3), 5, 4);
lean_closure_set(v___f_958_, 0, v_toPure_948_);
lean_closure_set(v___f_958_, 1, v_val_957_);
lean_closure_set(v___f_958_, 2, v_toBind_950_);
lean_closure_set(v___f_958_, 3, v___f_952_);
v___x_959_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7___closed__2));
v___x_960_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_checkInst___boxed), 8, 3);
lean_closure_set(v___x_960_, 0, v___x_959_);
lean_closure_set(v___x_960_, 1, v_val_957_);
lean_closure_set(v___x_960_, 2, v_inst_x27_949_);
v___x_961_ = lean_apply_2(v_inst_953_, lean_box(0), v___x_960_);
v___x_962_ = lean_apply_4(v_toBind_950_, lean_box(0), lean_box(0), v___x_961_, v___f_958_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4(lean_object* v_toPure_972_, lean_object* v_inst_973_, lean_object* v_toBind_974_, lean_object* v___f_975_, lean_object* v_inst_976_, lean_object* v_ring_977_){
_start:
{
lean_object* v_intCastFn_x3f_978_; 
v_intCastFn_x3f_978_ = lean_ctor_get(v_ring_977_, 11);
if (lean_obj_tag(v_intCastFn_x3f_978_) == 1)
{
lean_object* v_val_979_; lean_object* v___x_980_; 
lean_inc_ref(v_intCastFn_x3f_978_);
lean_dec_ref(v_ring_977_);
lean_dec(v_inst_976_);
lean_dec(v___f_975_);
lean_dec(v_toBind_974_);
lean_dec_ref(v_inst_973_);
v_val_979_ = lean_ctor_get(v_intCastFn_x3f_978_, 0);
lean_inc(v_val_979_);
lean_dec_ref(v_intCastFn_x3f_978_);
v___x_980_ = lean_apply_2(v_toPure_972_, lean_box(0), v_val_979_);
return v___x_980_;
}
else
{
lean_object* v_type_981_; lean_object* v_u_982_; lean_object* v_ringInst_983_; lean_object* v_canonExpr_984_; lean_object* v_synthInstance_x3f_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1006_; 
v_type_981_ = lean_ctor_get(v_ring_977_, 1);
lean_inc_ref(v_type_981_);
v_u_982_ = lean_ctor_get(v_ring_977_, 2);
lean_inc(v_u_982_);
v_ringInst_983_ = lean_ctor_get(v_ring_977_, 3);
lean_inc_ref(v_ringInst_983_);
lean_dec_ref(v_ring_977_);
v_canonExpr_984_ = lean_ctor_get(v_inst_973_, 0);
v_synthInstance_x3f_985_ = lean_ctor_get(v_inst_973_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_inst_973_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_987_ = v_inst_973_;
v_isShared_988_ = v_isSharedCheck_1006_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_synthInstance_x3f_985_);
lean_inc(v_canonExpr_984_);
lean_dec(v_inst_973_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1006_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_989_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__0));
v___x_990_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__1));
v___x_991_ = lean_box(0);
if (v_isShared_988_ == 0)
{
lean_ctor_set_tag(v___x_987_, 1);
lean_ctor_set(v___x_987_, 1, v___x_991_);
lean_ctor_set(v___x_987_, 0, v_u_982_);
v___x_993_ = v___x_987_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_u_982_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_991_);
v___x_993_ = v_reuseFailAlloc_1005_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
lean_object* v___x_994_; lean_object* v_inst_x27_995_; lean_object* v___x_996_; lean_object* v___f_997_; lean_object* v___f_998_; lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_instType_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_inc_ref_n(v___x_993_, 2);
v___x_994_ = l_Lean_mkConst(v___x_990_, v___x_993_);
lean_inc_ref_n(v_type_981_, 2);
v_inst_x27_995_ = l_Lean_mkAppB(v___x_994_, v_type_981_, v_ringInst_983_);
v___x_996_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__2));
lean_inc_n(v_toBind_974_, 2);
v___f_997_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_997_, 0, v___x_996_);
lean_closure_set(v___f_997_, 1, v___x_989_);
lean_closure_set(v___f_997_, 2, v___x_993_);
lean_closure_set(v___f_997_, 3, v_type_981_);
lean_closure_set(v___f_997_, 4, v_canonExpr_984_);
lean_closure_set(v___f_997_, 5, v_toBind_974_);
lean_closure_set(v___f_997_, 6, v___f_975_);
v___f_998_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg___lam__1), 2, 1);
lean_closure_set(v___f_998_, 0, v___f_997_);
lean_inc_ref(v___f_998_);
v___f_999_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__7), 7, 6);
lean_closure_set(v___f_999_, 0, v_toPure_972_);
lean_closure_set(v___f_999_, 1, v_inst_x27_995_);
lean_closure_set(v___f_999_, 2, v_toBind_974_);
lean_closure_set(v___f_999_, 3, v___f_998_);
lean_closure_set(v___f_999_, 4, v___f_998_);
lean_closure_set(v___f_999_, 5, v_inst_976_);
v___x_1000_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4___closed__3));
v___x_1001_ = l_Lean_mkConst(v___x_1000_, v___x_993_);
v_instType_1002_ = l_Lean_Expr_app___override(v___x_1001_, v_type_981_);
v___x_1003_ = lean_apply_1(v_synthInstance_x3f_985_, v_instType_1002_);
v___x_1004_ = lean_apply_4(v_toBind_974_, lean_box(0), lean_box(0), v___x_1003_, v___f_999_);
return v___x_1004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(lean_object* v_inst_1007_, lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_){
_start:
{
lean_object* v_toApplicative_1011_; lean_object* v_toBind_1012_; lean_object* v_getRing_1013_; lean_object* v_modifyRing_1014_; lean_object* v_toPure_1015_; lean_object* v___f_1016_; lean_object* v___f_1017_; lean_object* v___x_1018_; 
v_toApplicative_1011_ = lean_ctor_get(v_inst_1008_, 0);
lean_inc_ref(v_toApplicative_1011_);
v_toBind_1012_ = lean_ctor_get(v_inst_1008_, 1);
lean_inc_n(v_toBind_1012_, 3);
lean_dec_ref(v_inst_1008_);
v_getRing_1013_ = lean_ctor_get(v_inst_1010_, 0);
lean_inc(v_getRing_1013_);
v_modifyRing_1014_ = lean_ctor_get(v_inst_1010_, 1);
lean_inc(v_modifyRing_1014_);
lean_dec_ref(v_inst_1010_);
v_toPure_1015_ = lean_ctor_get(v_toApplicative_1011_, 1);
lean_inc_n(v_toPure_1015_, 2);
lean_dec_ref(v_toApplicative_1011_);
v___f_1016_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1016_, 0, v_toPure_1015_);
lean_closure_set(v___f_1016_, 1, v_modifyRing_1014_);
lean_closure_set(v___f_1016_, 2, v_toBind_1012_);
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getIntCastFn___redArg___lam__4), 6, 5);
lean_closure_set(v___f_1017_, 0, v_toPure_1015_);
lean_closure_set(v___f_1017_, 1, v_inst_1009_);
lean_closure_set(v___f_1017_, 2, v_toBind_1012_);
lean_closure_set(v___f_1017_, 3, v___f_1016_);
lean_closure_set(v___f_1017_, 4, v_inst_1007_);
v___x_1018_ = lean_apply_4(v_toBind_1012_, lean_box(0), lean_box(0), v_getRing_1013_, v___f_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getIntCastFn(lean_object* v_m_1019_, lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_inst_1022_, lean_object* v_inst_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_Meta_Sym_Arith_getIntCastFn___redArg(v_inst_1020_, v_inst_1021_, v_inst_1022_, v_inst_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0(lean_object* v_natCastFn_1025_, lean_object* v_s_1026_){
_start:
{
lean_object* v_id_1027_; lean_object* v_type_1028_; lean_object* v_u_1029_; lean_object* v_ringInst_1030_; lean_object* v_semiringInst_1031_; lean_object* v_charInst_x3f_1032_; lean_object* v_addFn_x3f_1033_; lean_object* v_mulFn_x3f_1034_; lean_object* v_subFn_x3f_1035_; lean_object* v_negFn_x3f_1036_; lean_object* v_powFn_x3f_1037_; lean_object* v_intCastFn_x3f_1038_; lean_object* v_one_x3f_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1047_; 
v_id_1027_ = lean_ctor_get(v_s_1026_, 0);
v_type_1028_ = lean_ctor_get(v_s_1026_, 1);
v_u_1029_ = lean_ctor_get(v_s_1026_, 2);
v_ringInst_1030_ = lean_ctor_get(v_s_1026_, 3);
v_semiringInst_1031_ = lean_ctor_get(v_s_1026_, 4);
v_charInst_x3f_1032_ = lean_ctor_get(v_s_1026_, 5);
v_addFn_x3f_1033_ = lean_ctor_get(v_s_1026_, 6);
v_mulFn_x3f_1034_ = lean_ctor_get(v_s_1026_, 7);
v_subFn_x3f_1035_ = lean_ctor_get(v_s_1026_, 8);
v_negFn_x3f_1036_ = lean_ctor_get(v_s_1026_, 9);
v_powFn_x3f_1037_ = lean_ctor_get(v_s_1026_, 10);
v_intCastFn_x3f_1038_ = lean_ctor_get(v_s_1026_, 11);
v_one_x3f_1039_ = lean_ctor_get(v_s_1026_, 13);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_s_1026_);
if (v_isSharedCheck_1047_ == 0)
{
lean_object* v_unused_1048_; 
v_unused_1048_ = lean_ctor_get(v_s_1026_, 12);
lean_dec(v_unused_1048_);
v___x_1041_ = v_s_1026_;
v_isShared_1042_ = v_isSharedCheck_1047_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_one_x3f_1039_);
lean_inc(v_intCastFn_x3f_1038_);
lean_inc(v_powFn_x3f_1037_);
lean_inc(v_negFn_x3f_1036_);
lean_inc(v_subFn_x3f_1035_);
lean_inc(v_mulFn_x3f_1034_);
lean_inc(v_addFn_x3f_1033_);
lean_inc(v_charInst_x3f_1032_);
lean_inc(v_semiringInst_1031_);
lean_inc(v_ringInst_1030_);
lean_inc(v_u_1029_);
lean_inc(v_type_1028_);
lean_inc(v_id_1027_);
lean_dec(v_s_1026_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1047_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1043_; lean_object* v___x_1045_; 
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_natCastFn_1025_);
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 12, v___x_1043_);
v___x_1045_ = v___x_1041_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(0, 14, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_id_1027_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_type_1028_);
lean_ctor_set(v_reuseFailAlloc_1046_, 2, v_u_1029_);
lean_ctor_set(v_reuseFailAlloc_1046_, 3, v_ringInst_1030_);
lean_ctor_set(v_reuseFailAlloc_1046_, 4, v_semiringInst_1031_);
lean_ctor_set(v_reuseFailAlloc_1046_, 5, v_charInst_x3f_1032_);
lean_ctor_set(v_reuseFailAlloc_1046_, 6, v_addFn_x3f_1033_);
lean_ctor_set(v_reuseFailAlloc_1046_, 7, v_mulFn_x3f_1034_);
lean_ctor_set(v_reuseFailAlloc_1046_, 8, v_subFn_x3f_1035_);
lean_ctor_set(v_reuseFailAlloc_1046_, 9, v_negFn_x3f_1036_);
lean_ctor_set(v_reuseFailAlloc_1046_, 10, v_powFn_x3f_1037_);
lean_ctor_set(v_reuseFailAlloc_1046_, 11, v_intCastFn_x3f_1038_);
lean_ctor_set(v_reuseFailAlloc_1046_, 12, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1046_, 13, v_one_x3f_1039_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1(lean_object* v_toPure_1049_, lean_object* v_natCastFn_1050_, lean_object* v_____r_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = lean_apply_2(v_toPure_1049_, lean_box(0), v_natCastFn_1050_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2(lean_object* v_toPure_1053_, lean_object* v_modifyRing_1054_, lean_object* v_toBind_1055_, lean_object* v_natCastFn_1056_){
_start:
{
lean_object* v___f_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
lean_inc_ref(v_natCastFn_1056_);
v___f_1057_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1057_, 0, v_natCastFn_1056_);
v___f_1058_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1058_, 0, v_toPure_1053_);
lean_closure_set(v___f_1058_, 1, v_natCastFn_1056_);
v___x_1059_ = lean_apply_1(v_modifyRing_1054_, v___f_1057_);
v___x_1060_ = lean_apply_4(v_toBind_1055_, lean_box(0), lean_box(0), v___x_1059_, v___f_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3(lean_object* v_toPure_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_toBind_1065_, lean_object* v___f_1066_, lean_object* v_ring_1067_){
_start:
{
lean_object* v_natCastFn_x3f_1068_; 
v_natCastFn_x3f_1068_ = lean_ctor_get(v_ring_1067_, 12);
if (lean_obj_tag(v_natCastFn_x3f_1068_) == 1)
{
lean_object* v_val_1069_; lean_object* v___x_1070_; 
lean_inc_ref(v_natCastFn_x3f_1068_);
lean_dec_ref(v_ring_1067_);
lean_dec(v___f_1066_);
lean_dec(v_toBind_1065_);
lean_dec_ref(v_inst_1064_);
lean_dec_ref(v_inst_1063_);
lean_dec(v_inst_1062_);
v_val_1069_ = lean_ctor_get(v_natCastFn_x3f_1068_, 0);
lean_inc(v_val_1069_);
lean_dec_ref(v_natCastFn_x3f_1068_);
v___x_1070_ = lean_apply_2(v_toPure_1061_, lean_box(0), v_val_1069_);
return v___x_1070_;
}
else
{
lean_object* v_type_1071_; lean_object* v_u_1072_; lean_object* v_semiringInst_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
lean_dec(v_toPure_1061_);
v_type_1071_ = lean_ctor_get(v_ring_1067_, 1);
lean_inc_ref(v_type_1071_);
v_u_1072_ = lean_ctor_get(v_ring_1067_, 2);
lean_inc(v_u_1072_);
v_semiringInst_1073_ = lean_ctor_get(v_ring_1067_, 4);
lean_inc_ref(v_semiringInst_1073_);
lean_dec_ref(v_ring_1067_);
v___x_1074_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1062_, v_inst_1063_, v_inst_1064_, v_u_1072_, v_type_1071_, v_semiringInst_1073_);
v___x_1075_ = lean_apply_4(v_toBind_1065_, lean_box(0), lean_box(0), v___x_1074_, v___f_1066_);
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_inst_1079_){
_start:
{
lean_object* v_toApplicative_1080_; lean_object* v_toBind_1081_; lean_object* v_getRing_1082_; lean_object* v_modifyRing_1083_; lean_object* v_toPure_1084_; lean_object* v___f_1085_; lean_object* v___f_1086_; lean_object* v___x_1087_; 
v_toApplicative_1080_ = lean_ctor_get(v_inst_1077_, 0);
v_toBind_1081_ = lean_ctor_get(v_inst_1077_, 1);
lean_inc_n(v_toBind_1081_, 3);
v_getRing_1082_ = lean_ctor_get(v_inst_1079_, 0);
lean_inc(v_getRing_1082_);
v_modifyRing_1083_ = lean_ctor_get(v_inst_1079_, 1);
lean_inc(v_modifyRing_1083_);
lean_dec_ref(v_inst_1079_);
v_toPure_1084_ = lean_ctor_get(v_toApplicative_1080_, 1);
lean_inc_n(v_toPure_1084_, 2);
v___f_1085_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1085_, 0, v_toPure_1084_);
lean_closure_set(v___f_1085_, 1, v_modifyRing_1083_);
lean_closure_set(v___f_1085_, 2, v_toBind_1081_);
v___f_1086_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__3), 7, 6);
lean_closure_set(v___f_1086_, 0, v_toPure_1084_);
lean_closure_set(v___f_1086_, 1, v_inst_1076_);
lean_closure_set(v___f_1086_, 2, v_inst_1077_);
lean_closure_set(v___f_1086_, 3, v_inst_1078_);
lean_closure_set(v___f_1086_, 4, v_toBind_1081_);
lean_closure_set(v___f_1086_, 5, v___f_1085_);
v___x_1087_ = lean_apply_4(v_toBind_1081_, lean_box(0), lean_box(0), v_getRing_1082_, v___f_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn(lean_object* v_m_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_Meta_Sym_Arith_getNatCastFn___redArg(v_inst_1089_, v_inst_1090_, v_inst_1091_, v_inst_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0(lean_object* v_invFn_1094_, lean_object* v_s_1095_){
_start:
{
lean_object* v_toRing_1096_; lean_object* v_semiringId_x3f_1097_; lean_object* v_commSemiringInst_1098_; lean_object* v_commRingInst_1099_; lean_object* v_noZeroDivInst_x3f_1100_; lean_object* v_fieldInst_x3f_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1109_; 
v_toRing_1096_ = lean_ctor_get(v_s_1095_, 0);
v_semiringId_x3f_1097_ = lean_ctor_get(v_s_1095_, 2);
v_commSemiringInst_1098_ = lean_ctor_get(v_s_1095_, 3);
v_commRingInst_1099_ = lean_ctor_get(v_s_1095_, 4);
v_noZeroDivInst_x3f_1100_ = lean_ctor_get(v_s_1095_, 5);
v_fieldInst_x3f_1101_ = lean_ctor_get(v_s_1095_, 6);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_s_1095_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v_s_1095_, 1);
lean_dec(v_unused_1110_);
v___x_1103_ = v_s_1095_;
v_isShared_1104_ = v_isSharedCheck_1109_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_fieldInst_x3f_1101_);
lean_inc(v_noZeroDivInst_x3f_1100_);
lean_inc(v_commRingInst_1099_);
lean_inc(v_commSemiringInst_1098_);
lean_inc(v_semiringId_x3f_1097_);
lean_inc(v_toRing_1096_);
lean_dec(v_s_1095_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1109_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1105_; lean_object* v___x_1107_; 
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_invFn_1094_);
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 1, v___x_1105_);
v___x_1107_ = v___x_1103_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_toRing_1096_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_semiringId_x3f_1097_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_commSemiringInst_1098_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_commRingInst_1099_);
lean_ctor_set(v_reuseFailAlloc_1108_, 5, v_noZeroDivInst_x3f_1100_);
lean_ctor_set(v_reuseFailAlloc_1108_, 6, v_fieldInst_x3f_1101_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1(lean_object* v_toPure_1111_, lean_object* v_invFn_1112_, lean_object* v_____r_1113_){
_start:
{
lean_object* v___x_1114_; 
v___x_1114_ = lean_apply_2(v_toPure_1111_, lean_box(0), v_invFn_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2(lean_object* v_toPure_1115_, lean_object* v_modifyCommRing_1116_, lean_object* v_toBind_1117_, lean_object* v_invFn_1118_){
_start:
{
lean_object* v___f_1119_; lean_object* v___f_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_inc_ref(v_invFn_1118_);
v___f_1119_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1119_, 0, v_invFn_1118_);
v___f_1120_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1120_, 0, v_toPure_1115_);
lean_closure_set(v___f_1120_, 1, v_invFn_1118_);
v___x_1121_ = lean_apply_1(v_modifyCommRing_1116_, v___f_1119_);
v___x_1122_ = lean_apply_4(v_toBind_1117_, lean_box(0), lean_box(0), v___x_1121_, v___f_1120_);
return v___x_1122_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1138_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__7));
v___x_1139_ = l_Lean_stringToMessageData(v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3(lean_object* v_toPure_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_toBind_1145_, lean_object* v___f_1146_, lean_object* v_ring_1147_){
_start:
{
lean_object* v_fieldInst_x3f_1148_; 
v_fieldInst_x3f_1148_ = lean_ctor_get(v_ring_1147_, 6);
if (lean_obj_tag(v_fieldInst_x3f_1148_) == 1)
{
lean_object* v_invFn_x3f_1149_; 
lean_inc_ref(v_fieldInst_x3f_1148_);
v_invFn_x3f_1149_ = lean_ctor_get(v_ring_1147_, 1);
if (lean_obj_tag(v_invFn_x3f_1149_) == 1)
{
lean_object* v_val_1150_; lean_object* v___x_1151_; 
lean_inc_ref(v_invFn_x3f_1149_);
lean_dec_ref(v_fieldInst_x3f_1148_);
lean_dec_ref(v_ring_1147_);
lean_dec(v___f_1146_);
lean_dec(v_toBind_1145_);
lean_dec_ref(v_inst_1144_);
lean_dec_ref(v_inst_1143_);
lean_dec_ref(v_inst_1142_);
lean_dec(v_inst_1141_);
v_val_1150_ = lean_ctor_get(v_invFn_x3f_1149_, 0);
lean_inc(v_val_1150_);
lean_dec_ref(v_invFn_x3f_1149_);
v___x_1151_ = lean_apply_2(v_toPure_1140_, lean_box(0), v_val_1150_);
return v___x_1151_;
}
else
{
lean_object* v_toRing_1152_; lean_object* v_val_1153_; lean_object* v_type_1154_; lean_object* v_u_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v_expectedInst_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
lean_dec(v_toPure_1140_);
v_toRing_1152_ = lean_ctor_get(v_ring_1147_, 0);
lean_inc_ref(v_toRing_1152_);
lean_dec_ref(v_ring_1147_);
v_val_1153_ = lean_ctor_get(v_fieldInst_x3f_1148_, 0);
lean_inc(v_val_1153_);
lean_dec_ref(v_fieldInst_x3f_1148_);
v_type_1154_ = lean_ctor_get(v_toRing_1152_, 1);
lean_inc_ref_n(v_type_1154_, 2);
v_u_1155_ = lean_ctor_get(v_toRing_1152_, 2);
lean_inc_n(v_u_1155_, 2);
lean_dec_ref(v_toRing_1152_);
v___x_1156_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__2));
v___x_1157_ = lean_box(0);
v___x_1158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1158_, 0, v_u_1155_);
lean_ctor_set(v___x_1158_, 1, v___x_1157_);
v___x_1159_ = l_Lean_mkConst(v___x_1156_, v___x_1158_);
v_expectedInst_1160_ = l_Lean_mkAppB(v___x_1159_, v_type_1154_, v_val_1153_);
v___x_1161_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__4));
v___x_1162_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__6));
v___x_1163_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkUnaryFn___redArg(v_inst_1141_, v_inst_1142_, v_inst_1143_, v_inst_1144_, v_type_1154_, v_u_1155_, v___x_1161_, v___x_1162_, v_expectedInst_1160_);
v___x_1164_ = lean_apply_4(v_toBind_1145_, lean_box(0), lean_box(0), v___x_1163_, v___f_1146_);
return v___x_1164_;
}
}
else
{
lean_object* v_toRing_1165_; lean_object* v_type_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_dec(v___f_1146_);
lean_dec(v_toBind_1145_);
lean_dec_ref(v_inst_1144_);
lean_dec(v_inst_1141_);
lean_dec(v_toPure_1140_);
v_toRing_1165_ = lean_ctor_get(v_ring_1147_, 0);
lean_inc_ref(v_toRing_1165_);
lean_dec_ref(v_ring_1147_);
v_type_1166_ = lean_ctor_get(v_toRing_1165_, 1);
lean_inc_ref(v_type_1166_);
lean_dec_ref(v_toRing_1165_);
v___x_1167_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8, &l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8_once, _init_l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3___closed__8);
v___x_1168_ = l_Lean_indentExpr(v_type_1166_);
v___x_1169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1167_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = l_Lean_throwError___redArg(v_inst_1143_, v_inst_1142_, v___x_1169_);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn___redArg(lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_){
_start:
{
lean_object* v_toApplicative_1176_; lean_object* v_toBind_1177_; lean_object* v_getCommRing_1178_; lean_object* v_modifyCommRing_1179_; lean_object* v_toPure_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___x_1183_; 
v_toApplicative_1176_ = lean_ctor_get(v_inst_1173_, 0);
v_toBind_1177_ = lean_ctor_get(v_inst_1173_, 1);
lean_inc_n(v_toBind_1177_, 3);
v_getCommRing_1178_ = lean_ctor_get(v_inst_1175_, 0);
lean_inc(v_getCommRing_1178_);
v_modifyCommRing_1179_ = lean_ctor_get(v_inst_1175_, 1);
lean_inc(v_modifyCommRing_1179_);
lean_dec_ref(v_inst_1175_);
v_toPure_1180_ = lean_ctor_get(v_toApplicative_1176_, 1);
lean_inc_n(v_toPure_1180_, 2);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1181_, 0, v_toPure_1180_);
lean_closure_set(v___f_1181_, 1, v_modifyCommRing_1179_);
lean_closure_set(v___f_1181_, 2, v_toBind_1177_);
v___f_1182_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getInvFn___redArg___lam__3), 8, 7);
lean_closure_set(v___f_1182_, 0, v_toPure_1180_);
lean_closure_set(v___f_1182_, 1, v_inst_1171_);
lean_closure_set(v___f_1182_, 2, v_inst_1172_);
lean_closure_set(v___f_1182_, 3, v_inst_1173_);
lean_closure_set(v___f_1182_, 4, v_inst_1174_);
lean_closure_set(v___f_1182_, 5, v_toBind_1177_);
lean_closure_set(v___f_1182_, 6, v___f_1181_);
v___x_1183_ = lean_apply_4(v_toBind_1177_, lean_box(0), lean_box(0), v_getCommRing_1178_, v___f_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getInvFn(lean_object* v_m_1184_, lean_object* v_inst_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_Meta_Sym_Arith_getInvFn___redArg(v_inst_1185_, v_inst_1186_, v_inst_1187_, v_inst_1188_, v_inst_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0(lean_object* v_addFn_1191_, lean_object* v_s_1192_){
_start:
{
lean_object* v_id_1193_; lean_object* v_type_1194_; lean_object* v_u_1195_; lean_object* v_semiringInst_1196_; lean_object* v_mulFn_x3f_1197_; lean_object* v_powFn_x3f_1198_; lean_object* v_natCastFn_x3f_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1207_; 
v_id_1193_ = lean_ctor_get(v_s_1192_, 0);
v_type_1194_ = lean_ctor_get(v_s_1192_, 1);
v_u_1195_ = lean_ctor_get(v_s_1192_, 2);
v_semiringInst_1196_ = lean_ctor_get(v_s_1192_, 3);
v_mulFn_x3f_1197_ = lean_ctor_get(v_s_1192_, 5);
v_powFn_x3f_1198_ = lean_ctor_get(v_s_1192_, 6);
v_natCastFn_x3f_1199_ = lean_ctor_get(v_s_1192_, 7);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_s_1192_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; 
v_unused_1208_ = lean_ctor_get(v_s_1192_, 4);
lean_dec(v_unused_1208_);
v___x_1201_ = v_s_1192_;
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_natCastFn_x3f_1199_);
lean_inc(v_powFn_x3f_1198_);
lean_inc(v_mulFn_x3f_1197_);
lean_inc(v_semiringInst_1196_);
lean_inc(v_u_1195_);
lean_inc(v_type_1194_);
lean_inc(v_id_1193_);
lean_dec(v_s_1192_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1207_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1205_; 
v___x_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1203_, 0, v_addFn_1191_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 4, v___x_1203_);
v___x_1205_ = v___x_1201_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_id_1193_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_type_1194_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_u_1195_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_semiringInst_1196_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1206_, 5, v_mulFn_x3f_1197_);
lean_ctor_set(v_reuseFailAlloc_1206_, 6, v_powFn_x3f_1198_);
lean_ctor_set(v_reuseFailAlloc_1206_, 7, v_natCastFn_x3f_1199_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2(lean_object* v_toPure_1209_, lean_object* v_modifySemiring_1210_, lean_object* v_toBind_1211_, lean_object* v_addFn_1212_){
_start:
{
lean_object* v___f_1213_; lean_object* v___f_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
lean_inc_ref(v_addFn_1212_);
v___f_1213_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1213_, 0, v_addFn_1212_);
v___f_1214_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1214_, 0, v_toPure_1209_);
lean_closure_set(v___f_1214_, 1, v_addFn_1212_);
v___x_1215_ = lean_apply_1(v_modifySemiring_1210_, v___f_1213_);
v___x_1216_ = lean_apply_4(v_toBind_1211_, lean_box(0), lean_box(0), v___x_1215_, v___f_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1(lean_object* v_toPure_1217_, lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_toBind_1222_, lean_object* v___f_1223_, lean_object* v_sr_1224_){
_start:
{
lean_object* v_addFn_x3f_1225_; 
v_addFn_x3f_1225_ = lean_ctor_get(v_sr_1224_, 4);
if (lean_obj_tag(v_addFn_x3f_1225_) == 1)
{
lean_object* v_val_1226_; lean_object* v___x_1227_; 
lean_inc_ref(v_addFn_x3f_1225_);
lean_dec_ref(v_sr_1224_);
lean_dec(v___f_1223_);
lean_dec(v_toBind_1222_);
lean_dec_ref(v_inst_1221_);
lean_dec_ref(v_inst_1220_);
lean_dec_ref(v_inst_1219_);
lean_dec(v_inst_1218_);
v_val_1226_ = lean_ctor_get(v_addFn_x3f_1225_, 0);
lean_inc(v_val_1226_);
lean_dec_ref(v_addFn_x3f_1225_);
v___x_1227_ = lean_apply_2(v_toPure_1217_, lean_box(0), v_val_1226_);
return v___x_1227_;
}
else
{
lean_object* v_type_1228_; lean_object* v_u_1229_; lean_object* v_semiringInst_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v_expectedInst_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
lean_dec(v_toPure_1217_);
v_type_1228_ = lean_ctor_get(v_sr_1224_, 1);
lean_inc_ref_n(v_type_1228_, 3);
v_u_1229_ = lean_ctor_get(v_sr_1224_, 2);
lean_inc_n(v_u_1229_, 2);
v_semiringInst_1230_ = lean_ctor_get(v_sr_1224_, 3);
lean_inc_ref(v_semiringInst_1230_);
lean_dec_ref(v_sr_1224_);
v___x_1231_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__1));
v___x_1232_ = lean_box(0);
v___x_1233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1233_, 0, v_u_1229_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
lean_inc_ref(v___x_1233_);
v___x_1234_ = l_Lean_mkConst(v___x_1231_, v___x_1233_);
v___x_1235_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__3));
v___x_1236_ = l_Lean_mkConst(v___x_1235_, v___x_1233_);
v___x_1237_ = l_Lean_mkAppB(v___x_1236_, v_type_1228_, v_semiringInst_1230_);
v_expectedInst_1238_ = l_Lean_mkAppB(v___x_1234_, v_type_1228_, v___x_1237_);
v___x_1239_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__5));
v___x_1240_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getAddFn___redArg___lam__3___closed__7));
v___x_1241_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1218_, v_inst_1219_, v_inst_1220_, v_inst_1221_, v_type_1228_, v_u_1229_, v___x_1239_, v___x_1240_, v_expectedInst_1238_);
v___x_1242_ = lean_apply_4(v_toBind_1222_, lean_box(0), lean_box(0), v___x_1241_, v___f_1223_);
return v___x_1242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_inst_1247_){
_start:
{
lean_object* v_toApplicative_1248_; lean_object* v_toBind_1249_; lean_object* v_getSemiring_1250_; lean_object* v_modifySemiring_1251_; lean_object* v_toPure_1252_; lean_object* v___f_1253_; lean_object* v___f_1254_; lean_object* v___x_1255_; 
v_toApplicative_1248_ = lean_ctor_get(v_inst_1245_, 0);
v_toBind_1249_ = lean_ctor_get(v_inst_1245_, 1);
lean_inc_n(v_toBind_1249_, 3);
v_getSemiring_1250_ = lean_ctor_get(v_inst_1247_, 0);
lean_inc(v_getSemiring_1250_);
v_modifySemiring_1251_ = lean_ctor_get(v_inst_1247_, 1);
lean_inc(v_modifySemiring_1251_);
lean_dec_ref(v_inst_1247_);
v_toPure_1252_ = lean_ctor_get(v_toApplicative_1248_, 1);
lean_inc_n(v_toPure_1252_, 2);
v___f_1253_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1253_, 0, v_toPure_1252_);
lean_closure_set(v___f_1253_, 1, v_modifySemiring_1251_);
lean_closure_set(v___f_1253_, 2, v_toBind_1249_);
v___f_1254_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1254_, 0, v_toPure_1252_);
lean_closure_set(v___f_1254_, 1, v_inst_1243_);
lean_closure_set(v___f_1254_, 2, v_inst_1244_);
lean_closure_set(v___f_1254_, 3, v_inst_1245_);
lean_closure_set(v___f_1254_, 4, v_inst_1246_);
lean_closure_set(v___f_1254_, 5, v_toBind_1249_);
lean_closure_set(v___f_1254_, 6, v___f_1253_);
v___x_1255_ = lean_apply_4(v_toBind_1249_, lean_box(0), lean_box(0), v_getSemiring_1250_, v___f_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getAddFn_x27(lean_object* v_m_1256_, lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Meta_Sym_Arith_getAddFn_x27___redArg(v_inst_1257_, v_inst_1258_, v_inst_1259_, v_inst_1260_, v_inst_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0(lean_object* v_mulFn_1263_, lean_object* v_s_1264_){
_start:
{
lean_object* v_id_1265_; lean_object* v_type_1266_; lean_object* v_u_1267_; lean_object* v_semiringInst_1268_; lean_object* v_addFn_x3f_1269_; lean_object* v_powFn_x3f_1270_; lean_object* v_natCastFn_x3f_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1279_; 
v_id_1265_ = lean_ctor_get(v_s_1264_, 0);
v_type_1266_ = lean_ctor_get(v_s_1264_, 1);
v_u_1267_ = lean_ctor_get(v_s_1264_, 2);
v_semiringInst_1268_ = lean_ctor_get(v_s_1264_, 3);
v_addFn_x3f_1269_ = lean_ctor_get(v_s_1264_, 4);
v_powFn_x3f_1270_ = lean_ctor_get(v_s_1264_, 6);
v_natCastFn_x3f_1271_ = lean_ctor_get(v_s_1264_, 7);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_s_1264_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v_s_1264_, 5);
lean_dec(v_unused_1280_);
v___x_1273_ = v_s_1264_;
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_natCastFn_x3f_1271_);
lean_inc(v_powFn_x3f_1270_);
lean_inc(v_addFn_x3f_1269_);
lean_inc(v_semiringInst_1268_);
lean_inc(v_u_1267_);
lean_inc(v_type_1266_);
lean_inc(v_id_1265_);
lean_dec(v_s_1264_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_mulFn_1263_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 5, v___x_1275_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_id_1265_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_type_1266_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_u_1267_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_semiringInst_1268_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v_addFn_x3f_1269_);
lean_ctor_set(v_reuseFailAlloc_1278_, 5, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1278_, 6, v_powFn_x3f_1270_);
lean_ctor_set(v_reuseFailAlloc_1278_, 7, v_natCastFn_x3f_1271_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2(lean_object* v_toPure_1281_, lean_object* v_modifySemiring_1282_, lean_object* v_toBind_1283_, lean_object* v_mulFn_1284_){
_start:
{
lean_object* v___f_1285_; lean_object* v___f_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_inc_ref(v_mulFn_1284_);
v___f_1285_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1285_, 0, v_mulFn_1284_);
v___f_1286_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1286_, 0, v_toPure_1281_);
lean_closure_set(v___f_1286_, 1, v_mulFn_1284_);
v___x_1287_ = lean_apply_1(v_modifySemiring_1282_, v___f_1285_);
v___x_1288_ = lean_apply_4(v_toBind_1283_, lean_box(0), lean_box(0), v___x_1287_, v___f_1286_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1(lean_object* v_toPure_1289_, lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_toBind_1294_, lean_object* v___f_1295_, lean_object* v_sr_1296_){
_start:
{
lean_object* v_mulFn_x3f_1297_; 
v_mulFn_x3f_1297_ = lean_ctor_get(v_sr_1296_, 5);
if (lean_obj_tag(v_mulFn_x3f_1297_) == 1)
{
lean_object* v_val_1298_; lean_object* v___x_1299_; 
lean_inc_ref(v_mulFn_x3f_1297_);
lean_dec_ref(v_sr_1296_);
lean_dec(v___f_1295_);
lean_dec(v_toBind_1294_);
lean_dec_ref(v_inst_1293_);
lean_dec_ref(v_inst_1292_);
lean_dec_ref(v_inst_1291_);
lean_dec(v_inst_1290_);
v_val_1298_ = lean_ctor_get(v_mulFn_x3f_1297_, 0);
lean_inc(v_val_1298_);
lean_dec_ref(v_mulFn_x3f_1297_);
v___x_1299_ = lean_apply_2(v_toPure_1289_, lean_box(0), v_val_1298_);
return v___x_1299_;
}
else
{
lean_object* v_type_1300_; lean_object* v_u_1301_; lean_object* v_semiringInst_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v_expectedInst_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec(v_toPure_1289_);
v_type_1300_ = lean_ctor_get(v_sr_1296_, 1);
lean_inc_ref_n(v_type_1300_, 3);
v_u_1301_ = lean_ctor_get(v_sr_1296_, 2);
lean_inc_n(v_u_1301_, 2);
v_semiringInst_1302_ = lean_ctor_get(v_sr_1296_, 3);
lean_inc_ref(v_semiringInst_1302_);
lean_dec_ref(v_sr_1296_);
v___x_1303_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__1));
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1305_, 0, v_u_1301_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
lean_inc_ref(v___x_1305_);
v___x_1306_ = l_Lean_mkConst(v___x_1303_, v___x_1305_);
v___x_1307_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__3));
v___x_1308_ = l_Lean_mkConst(v___x_1307_, v___x_1305_);
v___x_1309_ = l_Lean_mkAppB(v___x_1308_, v_type_1300_, v_semiringInst_1302_);
v_expectedInst_1310_ = l_Lean_mkAppB(v___x_1306_, v_type_1300_, v___x_1309_);
v___x_1311_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__5));
v___x_1312_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_getMulFn___redArg___lam__3___closed__7));
v___x_1313_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkBinHomoFn___redArg(v_inst_1290_, v_inst_1291_, v_inst_1292_, v_inst_1293_, v_type_1300_, v_u_1301_, v___x_1311_, v___x_1312_, v_expectedInst_1310_);
v___x_1314_ = lean_apply_4(v_toBind_1294_, lean_box(0), lean_box(0), v___x_1313_, v___f_1295_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_inst_1319_){
_start:
{
lean_object* v_toApplicative_1320_; lean_object* v_toBind_1321_; lean_object* v_getSemiring_1322_; lean_object* v_modifySemiring_1323_; lean_object* v_toPure_1324_; lean_object* v___f_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; 
v_toApplicative_1320_ = lean_ctor_get(v_inst_1317_, 0);
v_toBind_1321_ = lean_ctor_get(v_inst_1317_, 1);
lean_inc_n(v_toBind_1321_, 3);
v_getSemiring_1322_ = lean_ctor_get(v_inst_1319_, 0);
lean_inc(v_getSemiring_1322_);
v_modifySemiring_1323_ = lean_ctor_get(v_inst_1319_, 1);
lean_inc(v_modifySemiring_1323_);
lean_dec_ref(v_inst_1319_);
v_toPure_1324_ = lean_ctor_get(v_toApplicative_1320_, 1);
lean_inc_n(v_toPure_1324_, 2);
v___f_1325_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1325_, 0, v_toPure_1324_);
lean_closure_set(v___f_1325_, 1, v_modifySemiring_1323_);
lean_closure_set(v___f_1325_, 2, v_toBind_1321_);
v___f_1326_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1326_, 0, v_toPure_1324_);
lean_closure_set(v___f_1326_, 1, v_inst_1315_);
lean_closure_set(v___f_1326_, 2, v_inst_1316_);
lean_closure_set(v___f_1326_, 3, v_inst_1317_);
lean_closure_set(v___f_1326_, 4, v_inst_1318_);
lean_closure_set(v___f_1326_, 5, v_toBind_1321_);
lean_closure_set(v___f_1326_, 6, v___f_1325_);
v___x_1327_ = lean_apply_4(v_toBind_1321_, lean_box(0), lean_box(0), v_getSemiring_1322_, v___f_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getMulFn_x27(lean_object* v_m_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_){
_start:
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Lean_Meta_Sym_Arith_getMulFn_x27___redArg(v_inst_1329_, v_inst_1330_, v_inst_1331_, v_inst_1332_, v_inst_1333_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0(lean_object* v_powFn_1335_, lean_object* v_s_1336_){
_start:
{
lean_object* v_id_1337_; lean_object* v_type_1338_; lean_object* v_u_1339_; lean_object* v_semiringInst_1340_; lean_object* v_addFn_x3f_1341_; lean_object* v_mulFn_x3f_1342_; lean_object* v_natCastFn_x3f_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1351_; 
v_id_1337_ = lean_ctor_get(v_s_1336_, 0);
v_type_1338_ = lean_ctor_get(v_s_1336_, 1);
v_u_1339_ = lean_ctor_get(v_s_1336_, 2);
v_semiringInst_1340_ = lean_ctor_get(v_s_1336_, 3);
v_addFn_x3f_1341_ = lean_ctor_get(v_s_1336_, 4);
v_mulFn_x3f_1342_ = lean_ctor_get(v_s_1336_, 5);
v_natCastFn_x3f_1343_ = lean_ctor_get(v_s_1336_, 7);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_s_1336_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; 
v_unused_1352_ = lean_ctor_get(v_s_1336_, 6);
lean_dec(v_unused_1352_);
v___x_1345_ = v_s_1336_;
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_natCastFn_x3f_1343_);
lean_inc(v_mulFn_x3f_1342_);
lean_inc(v_addFn_x3f_1341_);
lean_inc(v_semiringInst_1340_);
lean_inc(v_u_1339_);
lean_inc(v_type_1338_);
lean_inc(v_id_1337_);
lean_dec(v_s_1336_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1351_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1349_; 
v___x_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1347_, 0, v_powFn_1335_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 6, v___x_1347_);
v___x_1349_ = v___x_1345_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_id_1337_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_type_1338_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_u_1339_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_semiringInst_1340_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_addFn_x3f_1341_);
lean_ctor_set(v_reuseFailAlloc_1350_, 5, v_mulFn_x3f_1342_);
lean_ctor_set(v_reuseFailAlloc_1350_, 6, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1350_, 7, v_natCastFn_x3f_1343_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2(lean_object* v_toPure_1353_, lean_object* v_modifySemiring_1354_, lean_object* v_toBind_1355_, lean_object* v_powFn_1356_){
_start:
{
lean_object* v___f_1357_; lean_object* v___f_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_inc_ref(v_powFn_1356_);
v___f_1357_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1357_, 0, v_powFn_1356_);
v___f_1358_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1358_, 0, v_toPure_1353_);
lean_closure_set(v___f_1358_, 1, v_powFn_1356_);
v___x_1359_ = lean_apply_1(v_modifySemiring_1354_, v___f_1357_);
v___x_1360_ = lean_apply_4(v_toBind_1355_, lean_box(0), lean_box(0), v___x_1359_, v___f_1358_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1(lean_object* v_toPure_1361_, lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_toBind_1366_, lean_object* v___f_1367_, lean_object* v_sr_1368_){
_start:
{
lean_object* v_powFn_x3f_1369_; 
v_powFn_x3f_1369_ = lean_ctor_get(v_sr_1368_, 6);
if (lean_obj_tag(v_powFn_x3f_1369_) == 1)
{
lean_object* v_val_1370_; lean_object* v___x_1371_; 
lean_inc_ref(v_powFn_x3f_1369_);
lean_dec_ref(v_sr_1368_);
lean_dec(v___f_1367_);
lean_dec(v_toBind_1366_);
lean_dec_ref(v_inst_1365_);
lean_dec_ref(v_inst_1364_);
lean_dec_ref(v_inst_1363_);
lean_dec(v_inst_1362_);
v_val_1370_ = lean_ctor_get(v_powFn_x3f_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref(v_powFn_x3f_1369_);
v___x_1371_ = lean_apply_2(v_toPure_1361_, lean_box(0), v_val_1370_);
return v___x_1371_;
}
else
{
lean_object* v_type_1372_; lean_object* v_u_1373_; lean_object* v_semiringInst_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v_toPure_1361_);
v_type_1372_ = lean_ctor_get(v_sr_1368_, 1);
lean_inc_ref(v_type_1372_);
v_u_1373_ = lean_ctor_get(v_sr_1368_, 2);
lean_inc(v_u_1373_);
v_semiringInst_1374_ = lean_ctor_get(v_sr_1368_, 3);
lean_inc_ref(v_semiringInst_1374_);
lean_dec_ref(v_sr_1368_);
v___x_1375_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkPowFn___redArg(v_inst_1362_, v_inst_1363_, v_inst_1364_, v_inst_1365_, v_u_1373_, v_type_1372_, v_semiringInst_1374_);
v___x_1376_ = lean_apply_4(v_toBind_1366_, lean_box(0), lean_box(0), v___x_1375_, v___f_1367_);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(lean_object* v_inst_1377_, lean_object* v_inst_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_inst_1381_){
_start:
{
lean_object* v_toApplicative_1382_; lean_object* v_toBind_1383_; lean_object* v_getSemiring_1384_; lean_object* v_modifySemiring_1385_; lean_object* v_toPure_1386_; lean_object* v___f_1387_; lean_object* v___f_1388_; lean_object* v___x_1389_; 
v_toApplicative_1382_ = lean_ctor_get(v_inst_1379_, 0);
v_toBind_1383_ = lean_ctor_get(v_inst_1379_, 1);
lean_inc_n(v_toBind_1383_, 3);
v_getSemiring_1384_ = lean_ctor_get(v_inst_1381_, 0);
lean_inc(v_getSemiring_1384_);
v_modifySemiring_1385_ = lean_ctor_get(v_inst_1381_, 1);
lean_inc(v_modifySemiring_1385_);
lean_dec_ref(v_inst_1381_);
v_toPure_1386_ = lean_ctor_get(v_toApplicative_1382_, 1);
lean_inc_n(v_toPure_1386_, 2);
v___f_1387_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1387_, 0, v_toPure_1386_);
lean_closure_set(v___f_1387_, 1, v_modifySemiring_1385_);
lean_closure_set(v___f_1387_, 2, v_toBind_1383_);
v___f_1388_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg___lam__1), 8, 7);
lean_closure_set(v___f_1388_, 0, v_toPure_1386_);
lean_closure_set(v___f_1388_, 1, v_inst_1377_);
lean_closure_set(v___f_1388_, 2, v_inst_1378_);
lean_closure_set(v___f_1388_, 3, v_inst_1379_);
lean_closure_set(v___f_1388_, 4, v_inst_1380_);
lean_closure_set(v___f_1388_, 5, v_toBind_1383_);
lean_closure_set(v___f_1388_, 6, v___f_1387_);
v___x_1389_ = lean_apply_4(v_toBind_1383_, lean_box(0), lean_box(0), v_getSemiring_1384_, v___f_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getPowFn_x27(lean_object* v_m_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_Meta_Sym_Arith_getPowFn_x27___redArg(v_inst_1391_, v_inst_1392_, v_inst_1393_, v_inst_1394_, v_inst_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0(lean_object* v_natCastFn_1397_, lean_object* v_s_1398_){
_start:
{
lean_object* v_id_1399_; lean_object* v_type_1400_; lean_object* v_u_1401_; lean_object* v_semiringInst_1402_; lean_object* v_addFn_x3f_1403_; lean_object* v_mulFn_x3f_1404_; lean_object* v_powFn_x3f_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1413_; 
v_id_1399_ = lean_ctor_get(v_s_1398_, 0);
v_type_1400_ = lean_ctor_get(v_s_1398_, 1);
v_u_1401_ = lean_ctor_get(v_s_1398_, 2);
v_semiringInst_1402_ = lean_ctor_get(v_s_1398_, 3);
v_addFn_x3f_1403_ = lean_ctor_get(v_s_1398_, 4);
v_mulFn_x3f_1404_ = lean_ctor_get(v_s_1398_, 5);
v_powFn_x3f_1405_ = lean_ctor_get(v_s_1398_, 6);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_s_1398_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v_s_1398_, 7);
lean_dec(v_unused_1414_);
v___x_1407_ = v_s_1398_;
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_powFn_x3f_1405_);
lean_inc(v_mulFn_x3f_1404_);
lean_inc(v_addFn_x3f_1403_);
lean_inc(v_semiringInst_1402_);
lean_inc(v_u_1401_);
lean_inc(v_type_1400_);
lean_inc(v_id_1399_);
lean_dec(v_s_1398_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1413_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v_natCastFn_1397_);
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 7, v___x_1409_);
v___x_1411_ = v___x_1407_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_id_1399_);
lean_ctor_set(v_reuseFailAlloc_1412_, 1, v_type_1400_);
lean_ctor_set(v_reuseFailAlloc_1412_, 2, v_u_1401_);
lean_ctor_set(v_reuseFailAlloc_1412_, 3, v_semiringInst_1402_);
lean_ctor_set(v_reuseFailAlloc_1412_, 4, v_addFn_x3f_1403_);
lean_ctor_set(v_reuseFailAlloc_1412_, 5, v_mulFn_x3f_1404_);
lean_ctor_set(v_reuseFailAlloc_1412_, 6, v_powFn_x3f_1405_);
lean_ctor_set(v_reuseFailAlloc_1412_, 7, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2(lean_object* v_toPure_1415_, lean_object* v_modifySemiring_1416_, lean_object* v_toBind_1417_, lean_object* v_natCastFn_1418_){
_start:
{
lean_object* v___f_1419_; lean_object* v___f_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
lean_inc_ref(v_natCastFn_1418_);
v___f_1419_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1419_, 0, v_natCastFn_1418_);
v___f_1420_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1420_, 0, v_toPure_1415_);
lean_closure_set(v___f_1420_, 1, v_natCastFn_1418_);
v___x_1421_ = lean_apply_1(v_modifySemiring_1416_, v___f_1419_);
v___x_1422_ = lean_apply_4(v_toBind_1417_, lean_box(0), lean_box(0), v___x_1421_, v___f_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1(lean_object* v_toPure_1423_, lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_toBind_1427_, lean_object* v___f_1428_, lean_object* v_sr_1429_){
_start:
{
lean_object* v_natCastFn_x3f_1430_; 
v_natCastFn_x3f_1430_ = lean_ctor_get(v_sr_1429_, 7);
if (lean_obj_tag(v_natCastFn_x3f_1430_) == 1)
{
lean_object* v_val_1431_; lean_object* v___x_1432_; 
lean_inc_ref(v_natCastFn_x3f_1430_);
lean_dec_ref(v_sr_1429_);
lean_dec(v___f_1428_);
lean_dec(v_toBind_1427_);
lean_dec_ref(v_inst_1426_);
lean_dec_ref(v_inst_1425_);
lean_dec(v_inst_1424_);
v_val_1431_ = lean_ctor_get(v_natCastFn_x3f_1430_, 0);
lean_inc(v_val_1431_);
lean_dec_ref(v_natCastFn_x3f_1430_);
v___x_1432_ = lean_apply_2(v_toPure_1423_, lean_box(0), v_val_1431_);
return v___x_1432_;
}
else
{
lean_object* v_type_1433_; lean_object* v_u_1434_; lean_object* v_semiringInst_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
lean_dec(v_toPure_1423_);
v_type_1433_ = lean_ctor_get(v_sr_1429_, 1);
lean_inc_ref(v_type_1433_);
v_u_1434_ = lean_ctor_get(v_sr_1429_, 2);
lean_inc(v_u_1434_);
v_semiringInst_1435_ = lean_ctor_get(v_sr_1429_, 3);
lean_inc_ref(v_semiringInst_1435_);
lean_dec_ref(v_sr_1429_);
v___x_1436_ = l___private_Lean_Meta_Sym_Arith_Functions_0__Lean_Meta_Sym_Arith_mkNatCastFn___redArg(v_inst_1424_, v_inst_1425_, v_inst_1426_, v_u_1434_, v_type_1433_, v_semiringInst_1435_);
v___x_1437_ = lean_apply_4(v_toBind_1427_, lean_box(0), lean_box(0), v___x_1436_, v___f_1428_);
return v___x_1437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(lean_object* v_inst_1438_, lean_object* v_inst_1439_, lean_object* v_inst_1440_, lean_object* v_inst_1441_){
_start:
{
lean_object* v_toApplicative_1442_; lean_object* v_toBind_1443_; lean_object* v_getSemiring_1444_; lean_object* v_modifySemiring_1445_; lean_object* v_toPure_1446_; lean_object* v___f_1447_; lean_object* v___f_1448_; lean_object* v___x_1449_; 
v_toApplicative_1442_ = lean_ctor_get(v_inst_1439_, 0);
v_toBind_1443_ = lean_ctor_get(v_inst_1439_, 1);
lean_inc_n(v_toBind_1443_, 3);
v_getSemiring_1444_ = lean_ctor_get(v_inst_1441_, 0);
lean_inc(v_getSemiring_1444_);
v_modifySemiring_1445_ = lean_ctor_get(v_inst_1441_, 1);
lean_inc(v_modifySemiring_1445_);
lean_dec_ref(v_inst_1441_);
v_toPure_1446_ = lean_ctor_get(v_toApplicative_1442_, 1);
lean_inc_n(v_toPure_1446_, 2);
v___f_1447_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__2), 4, 3);
lean_closure_set(v___f_1447_, 0, v_toPure_1446_);
lean_closure_set(v___f_1447_, 1, v_modifySemiring_1445_);
lean_closure_set(v___f_1447_, 2, v_toBind_1443_);
v___f_1448_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg___lam__1), 7, 6);
lean_closure_set(v___f_1448_, 0, v_toPure_1446_);
lean_closure_set(v___f_1448_, 1, v_inst_1438_);
lean_closure_set(v___f_1448_, 2, v_inst_1439_);
lean_closure_set(v___f_1448_, 3, v_inst_1440_);
lean_closure_set(v___f_1448_, 4, v_toBind_1443_);
lean_closure_set(v___f_1448_, 5, v___f_1447_);
v___x_1449_ = lean_apply_4(v_toBind_1443_, lean_box(0), lean_box(0), v_getSemiring_1444_, v___f_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_getNatCastFn_x27(lean_object* v_m_1450_, lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_Meta_Sym_Arith_getNatCastFn_x27___redArg(v_inst_1451_, v_inst_1452_, v_inst_1453_, v_inst_1454_);
return v___x_1455_;
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
