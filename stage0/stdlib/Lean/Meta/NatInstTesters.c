// Lean compiler output
// Module: Lean.Meta.NatInstTesters
// Imports: public import Lean.Meta.Basic
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
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstHMul;
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Nat_mkInstLE;
extern lean_object* l_Lean_Nat_mkInstHAdd;
extern lean_object* l_Lean_Nat_mkInstLT;
extern lean_object* l_Lean_Nat_mkInstAdd;
extern lean_object* l_Lean_Nat_mkInstMul;
static const lean_string_object l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "instOfNatNat"};
static const lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 8, 172, 44, 179, 254, 147, 95)}};
static const lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstAddNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instAddNat"};
static const lean_object* l_Lean_Meta_Structural_isInstAddNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstAddNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstAddNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstAddNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 164, 175, 25, 228, 165, 175, 183)}};
static const lean_object* l_Lean_Meta_Structural_isInstAddNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstAddNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstSubNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instSubNat"};
static const lean_object* l_Lean_Meta_Structural_isInstSubNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstSubNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstSubNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstSubNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 126, 242, 252, 139, 96, 73, 92)}};
static const lean_object* l_Lean_Meta_Structural_isInstSubNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstSubNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstMulNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instMulNat"};
static const lean_object* l_Lean_Meta_Structural_isInstMulNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstMulNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstMulNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstMulNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(251, 250, 177, 143, 4, 122, 150, 94)}};
static const lean_object* l_Lean_Meta_Structural_isInstMulNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstMulNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Structural_isInstDivNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDiv"};
static const lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstDivNat___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstDivNat___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(164, 220, 27, 244, 214, 254, 46, 170)}};
static const lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstModNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMod"};
static const lean_object* l_Lean_Meta_Structural_isInstModNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstModNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstModNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstModNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstModNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstModNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 28, 178, 185, 13, 18, 77, 86)}};
static const lean_object* l_Lean_Meta_Structural_isInstModNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstModNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "instNatPowNat"};
static const lean_object* l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 252, 138, 245, 102, 141, 87, 126)}};
static const lean_object* l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstPowNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instPowNat"};
static const lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstPowNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstPowNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstPowNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 228, 103, 52, 5, 80, 7, 4)}};
static const lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstPowNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHDiv"};
static const lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 70, 113, 198, 157, 211, 131, 18)}};
static const lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHModNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMod"};
static const lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHModNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHModNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHModNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 7, 29, 140, 31, 32, 204, 87)}};
static const lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHModNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHPow"};
static const lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 197, 76, 235, 199, 0, 254, 199)}};
static const lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstLTNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTNat"};
static const lean_object* l_Lean_Meta_Structural_isInstLTNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstLTNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstLTNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstLTNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 27, 201, 217, 48, 203, 85, 203)}};
static const lean_object* l_Lean_Meta_Structural_isInstLTNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstLTNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstLENat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLENat"};
static const lean_object* l_Lean_Meta_Structural_isInstLENat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstLENat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstLENat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstLENat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 47, 64, 46, 87, 101, 57, 105)}};
static const lean_object* l_Lean_Meta_Structural_isInstLENat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstLENat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDvd"};
static const lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 210, 229, 77, 176, 177, 112, 145)}};
static const lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstAndOpNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instAndOp"};
static const lean_object* l_Lean_Meta_Structural_isInstAndOpNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstAndOpNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstAndOpNat___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstDivNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstAndOpNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstAndOpNat___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstAndOpNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 213, 171, 194, 19, 60, 153, 32)}};
static const lean_object* l_Lean_Meta_Structural_isInstAndOpNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstAndOpNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAndOpNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAndOpNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAndOpNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAndOpNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHAndNat___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "instHAndOfAndOp"};
static const lean_object* l_Lean_Meta_Structural_isInstHAndNat___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHAndNat___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHAndNat___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHAndNat___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 130, 4, 53, 248, 235, 50, 226)}};
static const lean_object* l_Lean_Meta_Structural_isInstHAndNat___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHAndNat___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAndNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAndNat___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAndNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAndNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTNat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLENat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLENat___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object* v_e_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4_, v_a_5_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_25_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_25_ == 0)
{
v___x_14_ = v___x_11_;
v_isShared_15_ = v_isSharedCheck_25_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v___x_11_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_25_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = l_Lean_Expr_cleanupAnnotations(v_a_12_);
v___x_17_ = l_Lean_Expr_isApp(v___x_16_);
if (v___x_17_ == 0)
{
lean_dec_ref(v___x_16_);
lean_del_object(v___x_14_);
goto v___jp_7_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = l_Lean_Expr_appFnCleanup___redArg(v___x_16_);
v___x_19_ = ((lean_object*)(l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__1));
v___x_20_ = l_Lean_Expr_isConstOf(v___x_18_, v___x_19_);
lean_dec_ref(v___x_18_);
if (v___x_20_ == 0)
{
lean_del_object(v___x_14_);
goto v___jp_7_;
}
else
{
lean_object* v___x_21_; lean_object* v___x_23_; 
v___x_21_ = lean_box(v___x_20_);
if (v_isShared_15_ == 0)
{
lean_ctor_set(v___x_14_, 0, v___x_21_);
v___x_23_ = v___x_14_;
goto v_reusejp_22_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_21_);
v___x_23_ = v_reuseFailAlloc_24_;
goto v_reusejp_22_;
}
v_reusejp_22_:
{
return v___x_23_;
}
}
}
}
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
v_a_26_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_11_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_11_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_31_; 
if (v_isShared_29_ == 0)
{
v___x_31_ = v___x_28_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v_a_26_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
v___jp_7_:
{
uint8_t v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = 0;
v___x_9_ = lean_box(v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstOfNatNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4_ = stack[0].m_obj;
lean_object* v_a_5_ = stack[1].m_obj;
lean_object* v_res_34_;
v_res_34_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_e_4_, v_a_5_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg___boxed(lean_object* v_e_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_e_35_, v_a_36_);
lean_dec(v_a_36_);
return v_res_38_;
}
}
lean_object* l_Lean_Meta_Structural_isInstOfNatNat(lean_object* v_e_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_e_39_, v_a_41_);
return v___x_45_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstOfNatNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_39_ = stack[0].m_obj;
lean_object* v_a_40_ = stack[1].m_obj;
lean_object* v_a_41_ = stack[2].m_obj;
lean_object* v_a_42_ = stack[3].m_obj;
lean_object* v_a_43_ = stack[4].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lean_Meta_Structural_isInstOfNatNat(v_e_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatNat___boxed(lean_object* v_e_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_Structural_isInstOfNatNat(v_e_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
return v_res_53_;
}
}
lean_object* l_Lean_Meta_Structural_isInstAddNat___redArg(lean_object* v_e_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_57_, v_a_58_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_72_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_72_ == 0)
{
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_72_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_72_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_65_ = l_Lean_Expr_cleanupAnnotations(v_a_61_);
v___x_66_ = ((lean_object*)(l_Lean_Meta_Structural_isInstAddNat___redArg___closed__1));
v___x_67_ = l_Lean_Expr_isConstOf(v___x_65_, v___x_66_);
lean_dec_ref(v___x_65_);
v___x_68_ = lean_box(v___x_67_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_68_);
v___x_70_ = v___x_63_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
v_a_73_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_60_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_60_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstAddNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_57_ = stack[0].m_obj;
lean_object* v_a_58_ = stack[1].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_57_, v_a_58_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddNat___redArg___boxed(lean_object* v_e_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_82_, v_a_83_);
lean_dec(v_a_83_);
return v_res_85_;
}
}
lean_object* l_Lean_Meta_Structural_isInstAddNat(lean_object* v_e_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_86_, v_a_88_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstAddNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_86_ = stack[0].m_obj;
lean_object* v_a_87_ = stack[1].m_obj;
lean_object* v_a_88_ = stack[2].m_obj;
lean_object* v_a_89_ = stack[3].m_obj;
lean_object* v_a_90_ = stack[4].m_obj;
lean_object* v_res_93_;
v_res_93_ = l_Lean_Meta_Structural_isInstAddNat(v_e_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddNat___boxed(lean_object* v_e_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Meta_Structural_isInstAddNat(v_e_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
return v_res_100_;
}
}
lean_object* l_Lean_Meta_Structural_isInstSubNat___redArg(lean_object* v_e_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_104_, v_a_105_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_119_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_119_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_119_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_119_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
v___x_112_ = l_Lean_Expr_cleanupAnnotations(v_a_108_);
v___x_113_ = ((lean_object*)(l_Lean_Meta_Structural_isInstSubNat___redArg___closed__1));
v___x_114_ = l_Lean_Expr_isConstOf(v___x_112_, v___x_113_);
lean_dec_ref(v___x_112_);
v___x_115_ = lean_box(v___x_114_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_115_);
v___x_117_ = v___x_110_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_118_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
return v___x_117_;
}
}
}
else
{
lean_object* v_a_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_127_; 
v_a_120_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_127_ == 0)
{
v___x_122_ = v___x_107_;
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_a_120_);
lean_dec(v___x_107_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_127_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_125_; 
if (v_isShared_123_ == 0)
{
v___x_125_ = v___x_122_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_a_120_);
v___x_125_ = v_reuseFailAlloc_126_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstSubNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_104_ = stack[0].m_obj;
lean_object* v_a_105_ = stack[1].m_obj;
lean_object* v_res_128_;
v_res_128_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_e_104_, v_a_105_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubNat___redArg___boxed(lean_object* v_e_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_e_129_, v_a_130_);
lean_dec(v_a_130_);
return v_res_132_;
}
}
lean_object* l_Lean_Meta_Structural_isInstSubNat(lean_object* v_e_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_e_133_, v_a_135_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstSubNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_133_ = stack[0].m_obj;
lean_object* v_a_134_ = stack[1].m_obj;
lean_object* v_a_135_ = stack[2].m_obj;
lean_object* v_a_136_ = stack[3].m_obj;
lean_object* v_a_137_ = stack[4].m_obj;
lean_object* v_res_140_;
v_res_140_ = l_Lean_Meta_Structural_isInstSubNat(v_e_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
stack->m_obj
 = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubNat___boxed(lean_object* v_e_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_Meta_Structural_isInstSubNat(v_e_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
return v_res_147_;
}
}
lean_object* l_Lean_Meta_Structural_isInstMulNat___redArg(lean_object* v_e_151_, lean_object* v_a_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_151_, v_a_152_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_166_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_166_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_159_ = l_Lean_Expr_cleanupAnnotations(v_a_155_);
v___x_160_ = ((lean_object*)(l_Lean_Meta_Structural_isInstMulNat___redArg___closed__1));
v___x_161_ = l_Lean_Expr_isConstOf(v___x_159_, v___x_160_);
lean_dec_ref(v___x_159_);
v___x_162_ = lean_box(v___x_161_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_162_);
v___x_164_ = v___x_157_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_154_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_154_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstMulNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_151_ = stack[0].m_obj;
lean_object* v_a_152_ = stack[1].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_151_, v_a_152_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulNat___redArg___boxed(lean_object* v_e_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_176_, v_a_177_);
lean_dec(v_a_177_);
return v_res_179_;
}
}
lean_object* l_Lean_Meta_Structural_isInstMulNat(lean_object* v_e_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_180_, v_a_182_);
return v___x_186_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstMulNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_180_ = stack[0].m_obj;
lean_object* v_a_181_ = stack[1].m_obj;
lean_object* v_a_182_ = stack[2].m_obj;
lean_object* v_a_183_ = stack[3].m_obj;
lean_object* v_a_184_ = stack[4].m_obj;
lean_object* v_res_187_;
v_res_187_ = l_Lean_Meta_Structural_isInstMulNat(v_e_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulNat___boxed(lean_object* v_e_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_Meta_Structural_isInstMulNat(v_e_188_, v_a_189_, v_a_190_, v_a_191_, v_a_192_);
lean_dec(v_a_192_);
lean_dec_ref(v_a_191_);
lean_dec(v_a_190_);
lean_dec_ref(v_a_189_);
return v_res_194_;
}
}
lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg(lean_object* v_e_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_200_, v_a_201_);
if (lean_obj_tag(v___x_203_) == 0)
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_215_; 
v_a_204_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_215_ == 0)
{
v___x_206_ = v___x_203_;
v_isShared_207_ = v_isSharedCheck_215_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_203_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_215_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_208_ = l_Lean_Expr_cleanupAnnotations(v_a_204_);
v___x_209_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2));
v___x_210_ = l_Lean_Expr_isConstOf(v___x_208_, v___x_209_);
lean_dec_ref(v___x_208_);
v___x_211_ = lean_box(v___x_210_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_211_);
v___x_213_ = v___x_206_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
v_a_216_ = lean_ctor_get(v___x_203_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_203_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_203_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_203_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstDivNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_200_ = stack[0].m_obj;
lean_object* v_a_201_ = stack[1].m_obj;
lean_object* v_res_224_;
v_res_224_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_e_200_, v_a_201_);
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg___boxed(lean_object* v_e_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_e_225_, v_a_226_);
lean_dec(v_a_226_);
return v_res_228_;
}
}
lean_object* l_Lean_Meta_Structural_isInstDivNat(lean_object* v_e_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_e_229_, v_a_231_);
return v___x_235_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstDivNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_229_ = stack[0].m_obj;
lean_object* v_a_230_ = stack[1].m_obj;
lean_object* v_a_231_ = stack[2].m_obj;
lean_object* v_a_232_ = stack[3].m_obj;
lean_object* v_a_233_ = stack[4].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_Meta_Structural_isInstDivNat(v_e_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivNat___boxed(lean_object* v_e_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Meta_Structural_isInstDivNat(v_e_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
return v_res_243_;
}
}
lean_object* l_Lean_Meta_Structural_isInstModNat___redArg(lean_object* v_e_248_, lean_object* v_a_249_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_248_, v_a_249_);
if (lean_obj_tag(v___x_251_) == 0)
{
lean_object* v_a_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_263_; 
v_a_252_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_263_ == 0)
{
v___x_254_ = v___x_251_;
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_a_252_);
lean_dec(v___x_251_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_263_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
v___x_256_ = l_Lean_Expr_cleanupAnnotations(v_a_252_);
v___x_257_ = ((lean_object*)(l_Lean_Meta_Structural_isInstModNat___redArg___closed__1));
v___x_258_ = l_Lean_Expr_isConstOf(v___x_256_, v___x_257_);
lean_dec_ref(v___x_256_);
v___x_259_ = lean_box(v___x_258_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_259_);
v___x_261_ = v___x_254_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
v_a_264_ = lean_ctor_get(v___x_251_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_251_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_251_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_251_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstModNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_248_ = stack[0].m_obj;
lean_object* v_a_249_ = stack[1].m_obj;
lean_object* v_res_272_;
v_res_272_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_e_248_, v_a_249_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModNat___redArg___boxed(lean_object* v_e_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_e_273_, v_a_274_);
lean_dec(v_a_274_);
return v_res_276_;
}
}
lean_object* l_Lean_Meta_Structural_isInstModNat(lean_object* v_e_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_e_277_, v_a_279_);
return v___x_283_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstModNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_277_ = stack[0].m_obj;
lean_object* v_a_278_ = stack[1].m_obj;
lean_object* v_a_279_ = stack[2].m_obj;
lean_object* v_a_280_ = stack[3].m_obj;
lean_object* v_a_281_ = stack[4].m_obj;
lean_object* v_res_284_;
v_res_284_ = l_Lean_Meta_Structural_isInstModNat(v_e_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_);
stack->m_obj
 = v_res_284_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModNat___boxed(lean_object* v_e_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Meta_Structural_isInstModNat(v_e_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
return v_res_291_;
}
}
lean_object* l_Lean_Meta_Structural_isInstNatPowNat___redArg(lean_object* v_e_295_, lean_object* v_a_296_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_295_, v_a_296_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_310_; 
v_a_299_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_310_ == 0)
{
v___x_301_ = v___x_298_;
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_298_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_310_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_303_; lean_object* v___x_304_; uint8_t v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_303_ = l_Lean_Expr_cleanupAnnotations(v_a_299_);
v___x_304_ = ((lean_object*)(l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__1));
v___x_305_ = l_Lean_Expr_isConstOf(v___x_303_, v___x_304_);
lean_dec_ref(v___x_303_);
v___x_306_ = lean_box(v___x_305_);
if (v_isShared_302_ == 0)
{
lean_ctor_set(v___x_301_, 0, v___x_306_);
v___x_308_ = v___x_301_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_a_311_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_298_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_298_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstNatPowNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_295_ = stack[0].m_obj;
lean_object* v_a_296_ = stack[1].m_obj;
lean_object* v_res_319_;
v_res_319_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_e_295_, v_a_296_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowNat___redArg___boxed(lean_object* v_e_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_e_320_, v_a_321_);
lean_dec(v_a_321_);
return v_res_323_;
}
}
lean_object* l_Lean_Meta_Structural_isInstNatPowNat(lean_object* v_e_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_e_324_, v_a_326_);
return v___x_330_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstNatPowNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_324_ = stack[0].m_obj;
lean_object* v_a_325_ = stack[1].m_obj;
lean_object* v_a_326_ = stack[2].m_obj;
lean_object* v_a_327_ = stack[3].m_obj;
lean_object* v_a_328_ = stack[4].m_obj;
lean_object* v_res_331_;
v_res_331_ = l_Lean_Meta_Structural_isInstNatPowNat(v_e_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_);
stack->m_obj
 = v_res_331_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowNat___boxed(lean_object* v_e_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_res_338_; 
v_res_338_ = l_Lean_Meta_Structural_isInstNatPowNat(v_e_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
lean_dec(v_a_336_);
lean_dec_ref(v_a_335_);
lean_dec(v_a_334_);
lean_dec_ref(v_a_333_);
return v_res_338_;
}
}
lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg(lean_object* v_e_342_, lean_object* v_a_343_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_342_, v_a_343_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
v___x_351_ = l_Lean_Expr_cleanupAnnotations(v_a_350_);
v___x_352_ = l_Lean_Expr_isApp(v___x_351_);
if (v___x_352_ == 0)
{
lean_dec_ref(v___x_351_);
goto v___jp_345_;
}
else
{
lean_object* v_arg_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_arg_353_ = lean_ctor_get(v___x_351_, 1);
lean_inc_ref(v_arg_353_);
v___x_354_ = l_Lean_Expr_appFnCleanup___redArg(v___x_351_);
v___x_355_ = l_Lean_Expr_isApp(v___x_354_);
if (v___x_355_ == 0)
{
lean_dec_ref(v___x_354_);
lean_dec_ref(v_arg_353_);
goto v___jp_345_;
}
else
{
lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_356_ = l_Lean_Expr_appFnCleanup___redArg(v___x_354_);
v___x_357_ = ((lean_object*)(l_Lean_Meta_Structural_isInstPowNat___redArg___closed__1));
v___x_358_ = l_Lean_Expr_isConstOf(v___x_356_, v___x_357_);
lean_dec_ref(v___x_356_);
if (v___x_358_ == 0)
{
lean_dec_ref(v_arg_353_);
goto v___jp_345_;
}
else
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_arg_353_, v_a_343_);
return v___x_359_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_360_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_349_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_349_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
v___jp_345_:
{
uint8_t v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = 0;
v___x_347_ = lean_box(v___x_346_);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstPowNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_342_ = stack[0].m_obj;
lean_object* v_a_343_ = stack[1].m_obj;
lean_object* v_res_368_;
v_res_368_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_e_342_, v_a_343_);
stack->m_obj
 = v_res_368_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg___boxed(lean_object* v_e_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_e_369_, v_a_370_);
lean_dec(v_a_370_);
return v_res_372_;
}
}
lean_object* l_Lean_Meta_Structural_isInstPowNat(lean_object* v_e_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_e_373_, v_a_375_);
return v___x_379_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstPowNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_373_ = stack[0].m_obj;
lean_object* v_a_374_ = stack[1].m_obj;
lean_object* v_a_375_ = stack[2].m_obj;
lean_object* v_a_376_ = stack[3].m_obj;
lean_object* v_a_377_ = stack[4].m_obj;
lean_object* v_res_380_;
v_res_380_ = l_Lean_Meta_Structural_isInstPowNat(v_e_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_);
stack->m_obj
 = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat___boxed(lean_object* v_e_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Meta_Structural_isInstPowNat(v_e_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
return v_res_387_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object* v_e_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_391_, v_a_392_);
if (lean_obj_tag(v___x_398_) == 0)
{
lean_object* v_a_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
lean_dec_ref_known(v___x_398_, 1);
v___x_400_ = l_Lean_Expr_cleanupAnnotations(v_a_399_);
v___x_401_ = l_Lean_Expr_isApp(v___x_400_);
if (v___x_401_ == 0)
{
lean_dec_ref(v___x_400_);
goto v___jp_394_;
}
else
{
lean_object* v_arg_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_arg_402_ = lean_ctor_get(v___x_400_, 1);
lean_inc_ref(v_arg_402_);
v___x_403_ = l_Lean_Expr_appFnCleanup___redArg(v___x_400_);
v___x_404_ = l_Lean_Expr_isApp(v___x_403_);
if (v___x_404_ == 0)
{
lean_dec_ref(v___x_403_);
lean_dec_ref(v_arg_402_);
goto v___jp_394_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_405_ = l_Lean_Expr_appFnCleanup___redArg(v___x_403_);
v___x_406_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__1));
v___x_407_ = l_Lean_Expr_isConstOf(v___x_405_, v___x_406_);
lean_dec_ref(v___x_405_);
if (v___x_407_ == 0)
{
lean_dec_ref(v_arg_402_);
goto v___jp_394_;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_arg_402_, v_a_392_);
return v___x_408_;
}
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
v_a_409_ = lean_ctor_get(v___x_398_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_398_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_398_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
v___jp_394_:
{
uint8_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_395_ = 0;
v___x_396_ = lean_box(v___x_395_);
v___x_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
return v___x_397_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHAddNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_391_ = stack[0].m_obj;
lean_object* v_a_392_ = stack[1].m_obj;
lean_object* v_res_417_;
v_res_417_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_391_, v_a_392_);
stack->m_obj
 = v_res_417_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg___boxed(lean_object* v_e_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_418_, v_a_419_);
lean_dec(v_a_419_);
return v_res_421_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHAddNat(lean_object* v_e_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_422_, v_a_424_);
return v___x_428_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHAddNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_422_ = stack[0].m_obj;
lean_object* v_a_423_ = stack[1].m_obj;
lean_object* v_a_424_ = stack[2].m_obj;
lean_object* v_a_425_ = stack[3].m_obj;
lean_object* v_a_426_ = stack[4].m_obj;
lean_object* v_res_429_;
v_res_429_ = l_Lean_Meta_Structural_isInstHAddNat(v_e_422_, v_a_423_, v_a_424_, v_a_425_, v_a_426_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___boxed(lean_object* v_e_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_Structural_isInstHAddNat(v_e_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec_ref(v_a_431_);
return v_res_436_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg(lean_object* v_e_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_440_, v_a_441_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_a_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v___x_447_, 1);
v___x_449_ = l_Lean_Expr_cleanupAnnotations(v_a_448_);
v___x_450_ = l_Lean_Expr_isApp(v___x_449_);
if (v___x_450_ == 0)
{
lean_dec_ref(v___x_449_);
goto v___jp_443_;
}
else
{
lean_object* v_arg_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_arg_451_ = lean_ctor_get(v___x_449_, 1);
lean_inc_ref(v_arg_451_);
v___x_452_ = l_Lean_Expr_appFnCleanup___redArg(v___x_449_);
v___x_453_ = l_Lean_Expr_isApp(v___x_452_);
if (v___x_453_ == 0)
{
lean_dec_ref(v___x_452_);
lean_dec_ref(v_arg_451_);
goto v___jp_443_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = l_Lean_Expr_appFnCleanup___redArg(v___x_452_);
v___x_455_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__1));
v___x_456_ = l_Lean_Expr_isConstOf(v___x_454_, v___x_455_);
lean_dec_ref(v___x_454_);
if (v___x_456_ == 0)
{
lean_dec_ref(v_arg_451_);
goto v___jp_443_;
}
else
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_arg_451_, v_a_441_);
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_a_458_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_447_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_447_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_463_; 
if (v_isShared_461_ == 0)
{
v___x_463_ = v___x_460_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v_a_458_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
return v___x_463_;
}
}
}
v___jp_443_:
{
uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_444_ = 0;
v___x_445_ = lean_box(v___x_444_);
v___x_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
return v___x_446_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHSubNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_440_ = stack[0].m_obj;
lean_object* v_a_441_ = stack[1].m_obj;
lean_object* v_res_466_;
v_res_466_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_e_440_, v_a_441_);
stack->m_obj
 = v_res_466_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg___boxed(lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_e_467_, v_a_468_);
lean_dec(v_a_468_);
return v_res_470_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHSubNat(lean_object* v_e_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_e_471_, v_a_473_);
return v___x_477_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHSubNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_471_ = stack[0].m_obj;
lean_object* v_a_472_ = stack[1].m_obj;
lean_object* v_a_473_ = stack[2].m_obj;
lean_object* v_a_474_ = stack[3].m_obj;
lean_object* v_a_475_ = stack[4].m_obj;
lean_object* v_res_478_;
v_res_478_ = l_Lean_Meta_Structural_isInstHSubNat(v_e_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_);
stack->m_obj
 = v_res_478_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___boxed(lean_object* v_e_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Lean_Meta_Structural_isInstHSubNat(v_e_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
lean_dec(v_a_483_);
lean_dec_ref(v_a_482_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
return v_res_485_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object* v_e_489_, lean_object* v_a_490_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_489_, v_a_490_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = l_Lean_Expr_cleanupAnnotations(v_a_497_);
v___x_499_ = l_Lean_Expr_isApp(v___x_498_);
if (v___x_499_ == 0)
{
lean_dec_ref(v___x_498_);
goto v___jp_492_;
}
else
{
lean_object* v_arg_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_arg_500_ = lean_ctor_get(v___x_498_, 1);
lean_inc_ref(v_arg_500_);
v___x_501_ = l_Lean_Expr_appFnCleanup___redArg(v___x_498_);
v___x_502_ = l_Lean_Expr_isApp(v___x_501_);
if (v___x_502_ == 0)
{
lean_dec_ref(v___x_501_);
lean_dec_ref(v_arg_500_);
goto v___jp_492_;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = l_Lean_Expr_appFnCleanup___redArg(v___x_501_);
v___x_504_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__1));
v___x_505_ = l_Lean_Expr_isConstOf(v___x_503_, v___x_504_);
lean_dec_ref(v___x_503_);
if (v___x_505_ == 0)
{
lean_dec_ref(v_arg_500_);
goto v___jp_492_;
}
else
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_arg_500_, v_a_490_);
return v___x_506_;
}
}
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_a_507_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_496_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_496_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
v___jp_492_:
{
uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = 0;
v___x_494_ = lean_box(v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHMulNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_489_ = stack[0].m_obj;
lean_object* v_a_490_ = stack[1].m_obj;
lean_object* v_res_515_;
v_res_515_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_489_, v_a_490_);
stack->m_obj
 = v_res_515_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg___boxed(lean_object* v_e_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_516_, v_a_517_);
lean_dec(v_a_517_);
return v_res_519_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHMulNat(lean_object* v_e_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_520_, v_a_522_);
return v___x_526_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHMulNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_520_ = stack[0].m_obj;
lean_object* v_a_521_ = stack[1].m_obj;
lean_object* v_a_522_ = stack[2].m_obj;
lean_object* v_a_523_ = stack[3].m_obj;
lean_object* v_a_524_ = stack[4].m_obj;
lean_object* v_res_527_;
v_res_527_ = l_Lean_Meta_Structural_isInstHMulNat(v_e_520_, v_a_521_, v_a_522_, v_a_523_, v_a_524_);
stack->m_obj
 = v_res_527_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___boxed(lean_object* v_e_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Meta_Structural_isInstHMulNat(v_e_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec_ref(v_a_529_);
return v_res_534_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object* v_e_538_, lean_object* v_a_539_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_538_, v_a_539_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_547_ = l_Lean_Expr_cleanupAnnotations(v_a_546_);
v___x_548_ = l_Lean_Expr_isApp(v___x_547_);
if (v___x_548_ == 0)
{
lean_dec_ref(v___x_547_);
goto v___jp_541_;
}
else
{
lean_object* v_arg_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_arg_549_ = lean_ctor_get(v___x_547_, 1);
lean_inc_ref(v_arg_549_);
v___x_550_ = l_Lean_Expr_appFnCleanup___redArg(v___x_547_);
v___x_551_ = l_Lean_Expr_isApp(v___x_550_);
if (v___x_551_ == 0)
{
lean_dec_ref(v___x_550_);
lean_dec_ref(v_arg_549_);
goto v___jp_541_;
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = l_Lean_Expr_appFnCleanup___redArg(v___x_550_);
v___x_553_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__1));
v___x_554_ = l_Lean_Expr_isConstOf(v___x_552_, v___x_553_);
lean_dec_ref(v___x_552_);
if (v___x_554_ == 0)
{
lean_dec_ref(v_arg_549_);
goto v___jp_541_;
}
else
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_arg_549_, v_a_539_);
return v___x_555_;
}
}
}
}
else
{
lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_563_; 
v_a_556_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_563_ == 0)
{
v___x_558_ = v___x_545_;
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_545_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_563_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_561_; 
if (v_isShared_559_ == 0)
{
v___x_561_ = v___x_558_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_a_556_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
v___jp_541_:
{
uint8_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = 0;
v___x_543_ = lean_box(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHDivNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_538_ = stack[0].m_obj;
lean_object* v_a_539_ = stack[1].m_obj;
lean_object* v_res_564_;
v_res_564_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_e_538_, v_a_539_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg___boxed(lean_object* v_e_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_e_565_, v_a_566_);
lean_dec(v_a_566_);
return v_res_568_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHDivNat(lean_object* v_e_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_e_569_, v_a_571_);
return v___x_575_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHDivNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_569_ = stack[0].m_obj;
lean_object* v_a_570_ = stack[1].m_obj;
lean_object* v_a_571_ = stack[2].m_obj;
lean_object* v_a_572_ = stack[3].m_obj;
lean_object* v_a_573_ = stack[4].m_obj;
lean_object* v_res_576_;
v_res_576_ = l_Lean_Meta_Structural_isInstHDivNat(v_e_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_);
stack->m_obj
 = v_res_576_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___boxed(lean_object* v_e_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Meta_Structural_isInstHDivNat(v_e_577_, v_a_578_, v_a_579_, v_a_580_, v_a_581_);
lean_dec(v_a_581_);
lean_dec_ref(v_a_580_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
return v_res_583_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object* v_e_587_, lean_object* v_a_588_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_587_, v_a_588_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = l_Lean_Expr_cleanupAnnotations(v_a_595_);
v___x_597_ = l_Lean_Expr_isApp(v___x_596_);
if (v___x_597_ == 0)
{
lean_dec_ref(v___x_596_);
goto v___jp_590_;
}
else
{
lean_object* v_arg_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v_arg_598_ = lean_ctor_get(v___x_596_, 1);
lean_inc_ref(v_arg_598_);
v___x_599_ = l_Lean_Expr_appFnCleanup___redArg(v___x_596_);
v___x_600_ = l_Lean_Expr_isApp(v___x_599_);
if (v___x_600_ == 0)
{
lean_dec_ref(v___x_599_);
lean_dec_ref(v_arg_598_);
goto v___jp_590_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = l_Lean_Expr_appFnCleanup___redArg(v___x_599_);
v___x_602_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHModNat___redArg___closed__1));
v___x_603_ = l_Lean_Expr_isConstOf(v___x_601_, v___x_602_);
lean_dec_ref(v___x_601_);
if (v___x_603_ == 0)
{
lean_dec_ref(v_arg_598_);
goto v___jp_590_;
}
else
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_arg_598_, v_a_588_);
return v___x_604_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
v_a_605_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_594_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_594_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
v___jp_590_:
{
uint8_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_591_ = 0;
v___x_592_ = lean_box(v___x_591_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
return v___x_593_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHModNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_587_ = stack[0].m_obj;
lean_object* v_a_588_ = stack[1].m_obj;
lean_object* v_res_613_;
v_res_613_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_e_587_, v_a_588_);
stack->m_obj
 = v_res_613_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg___boxed(lean_object* v_e_614_, lean_object* v_a_615_, lean_object* v_a_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_e_614_, v_a_615_);
lean_dec(v_a_615_);
return v_res_617_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHModNat(lean_object* v_e_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_e_618_, v_a_620_);
return v___x_624_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHModNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_618_ = stack[0].m_obj;
lean_object* v_a_619_ = stack[1].m_obj;
lean_object* v_a_620_ = stack[2].m_obj;
lean_object* v_a_621_ = stack[3].m_obj;
lean_object* v_a_622_ = stack[4].m_obj;
lean_object* v_res_625_;
v_res_625_ = l_Lean_Meta_Structural_isInstHModNat(v_e_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___boxed(lean_object* v_e_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_Meta_Structural_isInstHModNat(v_e_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_632_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object* v_e_636_, lean_object* v_a_637_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_636_, v_a_637_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = l_Lean_Expr_cleanupAnnotations(v_a_644_);
v___x_646_ = l_Lean_Expr_isApp(v___x_645_);
if (v___x_646_ == 0)
{
lean_dec_ref(v___x_645_);
goto v___jp_639_;
}
else
{
lean_object* v_arg_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_arg_647_ = lean_ctor_get(v___x_645_, 1);
lean_inc_ref(v_arg_647_);
v___x_648_ = l_Lean_Expr_appFnCleanup___redArg(v___x_645_);
v___x_649_ = l_Lean_Expr_isApp(v___x_648_);
if (v___x_649_ == 0)
{
lean_dec_ref(v___x_648_);
lean_dec_ref(v_arg_647_);
goto v___jp_639_;
}
else
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = l_Lean_Expr_appFnCleanup___redArg(v___x_648_);
v___x_651_ = l_Lean_Expr_isApp(v___x_650_);
if (v___x_651_ == 0)
{
lean_dec_ref(v___x_650_);
lean_dec_ref(v_arg_647_);
goto v___jp_639_;
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_652_ = l_Lean_Expr_appFnCleanup___redArg(v___x_650_);
v___x_653_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__1));
v___x_654_ = l_Lean_Expr_isConstOf(v___x_652_, v___x_653_);
lean_dec_ref(v___x_652_);
if (v___x_654_ == 0)
{
lean_dec_ref(v_arg_647_);
goto v___jp_639_;
}
else
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_arg_647_, v_a_637_);
return v___x_655_;
}
}
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_643_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_643_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
v___jp_639_:
{
uint8_t v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = 0;
v___x_641_ = lean_box(v___x_640_);
v___x_642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_642_, 0, v___x_641_);
return v___x_642_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHPowNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_636_ = stack[0].m_obj;
lean_object* v_a_637_ = stack[1].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_e_636_, v_a_637_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg___boxed(lean_object* v_e_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_e_665_, v_a_666_);
lean_dec(v_a_666_);
return v_res_668_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHPowNat(lean_object* v_e_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_e_669_, v_a_671_);
return v___x_675_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHPowNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_669_ = stack[0].m_obj;
lean_object* v_a_670_ = stack[1].m_obj;
lean_object* v_a_671_ = stack[2].m_obj;
lean_object* v_a_672_ = stack[3].m_obj;
lean_object* v_a_673_ = stack[4].m_obj;
lean_object* v_res_676_;
v_res_676_ = l_Lean_Meta_Structural_isInstHPowNat(v_e_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
stack->m_obj
 = v_res_676_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___boxed(lean_object* v_e_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Meta_Structural_isInstHPowNat(v_e_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
return v_res_683_;
}
}
lean_object* l_Lean_Meta_Structural_isInstLTNat___redArg(lean_object* v_e_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_687_, v_a_688_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_702_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_702_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_702_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_702_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; lean_object* v___x_698_; lean_object* v___x_700_; 
v___x_695_ = l_Lean_Expr_cleanupAnnotations(v_a_691_);
v___x_696_ = ((lean_object*)(l_Lean_Meta_Structural_isInstLTNat___redArg___closed__1));
v___x_697_ = l_Lean_Expr_isConstOf(v___x_695_, v___x_696_);
lean_dec_ref(v___x_695_);
v___x_698_ = lean_box(v___x_697_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_698_);
v___x_700_ = v___x_693_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_698_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_a_703_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_690_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_690_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstLTNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_687_ = stack[0].m_obj;
lean_object* v_a_688_ = stack[1].m_obj;
lean_object* v_res_711_;
v_res_711_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_687_, v_a_688_);
stack->m_obj
 = v_res_711_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___redArg___boxed(lean_object* v_e_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_712_, v_a_713_);
lean_dec(v_a_713_);
return v_res_715_;
}
}
lean_object* l_Lean_Meta_Structural_isInstLTNat(lean_object* v_e_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_716_, v_a_718_);
return v___x_722_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstLTNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_716_ = stack[0].m_obj;
lean_object* v_a_717_ = stack[1].m_obj;
lean_object* v_a_718_ = stack[2].m_obj;
lean_object* v_a_719_ = stack[3].m_obj;
lean_object* v_a_720_ = stack[4].m_obj;
lean_object* v_res_723_;
v_res_723_ = l_Lean_Meta_Structural_isInstLTNat(v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
stack->m_obj
 = v_res_723_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___boxed(lean_object* v_e_724_, lean_object* v_a_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Meta_Structural_isInstLTNat(v_e_724_, v_a_725_, v_a_726_, v_a_727_, v_a_728_);
lean_dec(v_a_728_);
lean_dec_ref(v_a_727_);
lean_dec(v_a_726_);
lean_dec_ref(v_a_725_);
return v_res_730_;
}
}
lean_object* l_Lean_Meta_Structural_isInstLENat___redArg(lean_object* v_e_734_, lean_object* v_a_735_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_734_, v_a_735_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_749_; 
v_a_738_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_749_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_749_ == 0)
{
v___x_740_ = v___x_737_;
v_isShared_741_ = v_isSharedCheck_749_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_749_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_742_ = l_Lean_Expr_cleanupAnnotations(v_a_738_);
v___x_743_ = ((lean_object*)(l_Lean_Meta_Structural_isInstLENat___redArg___closed__1));
v___x_744_ = l_Lean_Expr_isConstOf(v___x_742_, v___x_743_);
lean_dec_ref(v___x_742_);
v___x_745_ = lean_box(v___x_744_);
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_745_);
v___x_747_ = v___x_740_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_745_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
else
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
v_a_750_ = lean_ctor_get(v___x_737_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_737_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_737_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_737_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstLENat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_734_ = stack[0].m_obj;
lean_object* v_a_735_ = stack[1].m_obj;
lean_object* v_res_758_;
v_res_758_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_734_, v_a_735_);
stack->m_obj
 = v_res_758_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___redArg___boxed(lean_object* v_e_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_759_, v_a_760_);
lean_dec(v_a_760_);
return v_res_762_;
}
}
lean_object* l_Lean_Meta_Structural_isInstLENat(lean_object* v_e_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_763_, v_a_765_);
return v___x_769_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstLENat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_763_ = stack[0].m_obj;
lean_object* v_a_764_ = stack[1].m_obj;
lean_object* v_a_765_ = stack[2].m_obj;
lean_object* v_a_766_ = stack[3].m_obj;
lean_object* v_a_767_ = stack[4].m_obj;
lean_object* v_res_770_;
v_res_770_ = l_Lean_Meta_Structural_isInstLENat(v_e_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_);
stack->m_obj
 = v_res_770_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___boxed(lean_object* v_e_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Meta_Structural_isInstLENat(v_e_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
return v_res_777_;
}
}
lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg(lean_object* v_e_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_782_, v_a_783_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_797_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_797_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_797_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_797_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_790_ = l_Lean_Expr_cleanupAnnotations(v_a_786_);
v___x_791_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1));
v___x_792_ = l_Lean_Expr_isConstOf(v___x_790_, v___x_791_);
lean_dec_ref(v___x_790_);
v___x_793_ = lean_box(v___x_792_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_793_);
v___x_795_ = v___x_788_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
v_a_798_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_785_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_785_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstDvdNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_782_ = stack[0].m_obj;
lean_object* v_a_783_ = stack[1].m_obj;
lean_object* v_res_806_;
v_res_806_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_e_782_, v_a_783_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg___boxed(lean_object* v_e_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_e_807_, v_a_808_);
lean_dec(v_a_808_);
return v_res_810_;
}
}
lean_object* l_Lean_Meta_Structural_isInstDvdNat(lean_object* v_e_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_e_811_, v_a_813_);
return v___x_817_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstDvdNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_811_ = stack[0].m_obj;
lean_object* v_a_812_ = stack[1].m_obj;
lean_object* v_a_813_ = stack[2].m_obj;
lean_object* v_a_814_ = stack[3].m_obj;
lean_object* v_a_815_ = stack[4].m_obj;
lean_object* v_res_818_;
v_res_818_ = l_Lean_Meta_Structural_isInstDvdNat(v_e_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
stack->m_obj
 = v_res_818_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___boxed(lean_object* v_e_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_Meta_Structural_isInstDvdNat(v_e_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
return v_res_825_;
}
}
lean_object* l_Lean_Meta_Structural_isInstAndOpNat___redArg(lean_object* v_e_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; 
v___x_833_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_830_, v_a_831_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_845_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_845_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_845_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_845_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_845_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_838_ = l_Lean_Expr_cleanupAnnotations(v_a_834_);
v___x_839_ = ((lean_object*)(l_Lean_Meta_Structural_isInstAndOpNat___redArg___closed__1));
v___x_840_ = l_Lean_Expr_isConstOf(v___x_838_, v___x_839_);
lean_dec_ref(v___x_838_);
v___x_841_ = lean_box(v___x_840_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v___x_841_);
v___x_843_ = v___x_836_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
v_a_846_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_833_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_833_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstAndOpNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_830_ = stack[0].m_obj;
lean_object* v_a_831_ = stack[1].m_obj;
lean_object* v_res_854_;
v_res_854_ = l_Lean_Meta_Structural_isInstAndOpNat___redArg(v_e_830_, v_a_831_);
stack->m_obj
 = v_res_854_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAndOpNat___redArg___boxed(lean_object* v_e_855_, lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_Meta_Structural_isInstAndOpNat___redArg(v_e_855_, v_a_856_);
lean_dec(v_a_856_);
return v_res_858_;
}
}
lean_object* l_Lean_Meta_Structural_isInstAndOpNat(lean_object* v_e_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Meta_Structural_isInstAndOpNat___redArg(v_e_859_, v_a_861_);
return v___x_865_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstAndOpNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_859_ = stack[0].m_obj;
lean_object* v_a_860_ = stack[1].m_obj;
lean_object* v_a_861_ = stack[2].m_obj;
lean_object* v_a_862_ = stack[3].m_obj;
lean_object* v_a_863_ = stack[4].m_obj;
lean_object* v_res_866_;
v_res_866_ = l_Lean_Meta_Structural_isInstAndOpNat(v_e_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAndOpNat___boxed(lean_object* v_e_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_Structural_isInstAndOpNat(v_e_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
return v_res_873_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHAndNat___redArg(lean_object* v_e_877_, lean_object* v_a_878_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_877_, v_a_878_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v___x_886_ = l_Lean_Expr_cleanupAnnotations(v_a_885_);
v___x_887_ = l_Lean_Expr_isApp(v___x_886_);
if (v___x_887_ == 0)
{
lean_dec_ref(v___x_886_);
goto v___jp_880_;
}
else
{
lean_object* v_arg_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v_arg_888_ = lean_ctor_get(v___x_886_, 1);
lean_inc_ref(v_arg_888_);
v___x_889_ = l_Lean_Expr_appFnCleanup___redArg(v___x_886_);
v___x_890_ = l_Lean_Expr_isApp(v___x_889_);
if (v___x_890_ == 0)
{
lean_dec_ref(v___x_889_);
lean_dec_ref(v_arg_888_);
goto v___jp_880_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = l_Lean_Expr_appFnCleanup___redArg(v___x_889_);
v___x_892_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHAndNat___redArg___closed__1));
v___x_893_ = l_Lean_Expr_isConstOf(v___x_891_, v___x_892_);
lean_dec_ref(v___x_891_);
if (v___x_893_ == 0)
{
lean_dec_ref(v_arg_888_);
goto v___jp_880_;
}
else
{
lean_object* v___x_894_; 
v___x_894_ = l_Lean_Meta_Structural_isInstAndOpNat___redArg(v_arg_888_, v_a_878_);
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_884_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_884_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
v___jp_880_:
{
uint8_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = 0;
v___x_882_ = lean_box(v___x_881_);
v___x_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
return v___x_883_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHAndNat___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_877_ = stack[0].m_obj;
lean_object* v_a_878_ = stack[1].m_obj;
lean_object* v_res_903_;
v_res_903_ = l_Lean_Meta_Structural_isInstHAndNat___redArg(v_e_877_, v_a_878_);
stack->m_obj
 = v_res_903_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAndNat___redArg___boxed(lean_object* v_e_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Meta_Structural_isInstHAndNat___redArg(v_e_904_, v_a_905_);
lean_dec(v_a_905_);
return v_res_907_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHAndNat(lean_object* v_e_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_Lean_Meta_Structural_isInstHAndNat___redArg(v_e_908_, v_a_910_);
return v___x_914_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHAndNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_908_ = stack[0].m_obj;
lean_object* v_a_909_ = stack[1].m_obj;
lean_object* v_a_910_ = stack[2].m_obj;
lean_object* v_a_911_ = stack[3].m_obj;
lean_object* v_a_912_ = stack[4].m_obj;
lean_object* v_res_915_;
v_res_915_ = l_Lean_Meta_Structural_isInstHAndNat(v_e_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_);
stack->m_obj
 = v_res_915_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAndNat___boxed(lean_object* v_e_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Meta_Structural_isInstHAndNat(v_e_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_922_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstAddNat(lean_object* v_e_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_929_; 
lean_inc_ref(v_e_923_);
v___x_929_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_923_, v_a_925_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; uint8_t v___x_931_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v___x_931_ = lean_unbox(v_a_930_);
if (v___x_931_ == 0)
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref_known(v___x_929_, 1);
v___x_932_ = l_Lean_Nat_mkInstAdd;
v___x_933_ = l_Lean_Meta_isDefEqI(v_e_923_, v___x_932_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
return v___x_933_;
}
else
{
lean_dec_ref(v_e_923_);
return v___x_929_;
}
}
else
{
lean_dec_ref(v_e_923_);
return v___x_929_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstAddNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_923_ = stack[0].m_obj;
lean_object* v_a_924_ = stack[1].m_obj;
lean_object* v_a_925_ = stack[2].m_obj;
lean_object* v_a_926_ = stack[3].m_obj;
lean_object* v_a_927_ = stack[4].m_obj;
lean_object* v_res_934_;
v_res_934_ = l_Lean_Meta_DefEq_isInstAddNat(v_e_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddNat___boxed(lean_object* v_e_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Meta_DefEq_isInstAddNat(v_e_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
return v_res_941_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstHAddNat(lean_object* v_e_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_948_; 
lean_inc_ref(v_e_942_);
v___x_948_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_942_, v_a_944_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; uint8_t v___x_950_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
v___x_950_ = lean_unbox(v_a_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec_ref_known(v___x_948_, 1);
v___x_951_ = l_Lean_Nat_mkInstHAdd;
v___x_952_ = l_Lean_Meta_isDefEqI(v_e_942_, v___x_951_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
return v___x_952_;
}
else
{
lean_dec_ref(v_e_942_);
return v___x_948_;
}
}
else
{
lean_dec_ref(v_e_942_);
return v___x_948_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstHAddNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_942_ = stack[0].m_obj;
lean_object* v_a_943_ = stack[1].m_obj;
lean_object* v_a_944_ = stack[2].m_obj;
lean_object* v_a_945_ = stack[3].m_obj;
lean_object* v_a_946_ = stack[4].m_obj;
lean_object* v_res_953_;
v_res_953_ = l_Lean_Meta_DefEq_isInstHAddNat(v_e_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_);
stack->m_obj
 = v_res_953_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddNat___boxed(lean_object* v_e_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_Meta_DefEq_isInstHAddNat(v_e_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
return v_res_960_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstMulNat(lean_object* v_e_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; 
lean_inc_ref(v_e_961_);
v___x_967_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_961_, v_a_963_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; uint8_t v___x_969_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v___x_969_ = lean_unbox(v_a_968_);
if (v___x_969_ == 0)
{
lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec_ref_known(v___x_967_, 1);
v___x_970_ = l_Lean_Nat_mkInstMul;
v___x_971_ = l_Lean_Meta_isDefEqI(v_e_961_, v___x_970_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_971_;
}
else
{
lean_dec_ref(v_e_961_);
return v___x_967_;
}
}
else
{
lean_dec_ref(v_e_961_);
return v___x_967_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstMulNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_961_ = stack[0].m_obj;
lean_object* v_a_962_ = stack[1].m_obj;
lean_object* v_a_963_ = stack[2].m_obj;
lean_object* v_a_964_ = stack[3].m_obj;
lean_object* v_a_965_ = stack[4].m_obj;
lean_object* v_res_972_;
v_res_972_ = l_Lean_Meta_DefEq_isInstMulNat(v_e_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
stack->m_obj
 = v_res_972_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulNat___boxed(lean_object* v_e_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Meta_DefEq_isInstMulNat(v_e_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
lean_dec(v_a_975_);
lean_dec_ref(v_a_974_);
return v_res_979_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstHMulNat(lean_object* v_e_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; 
lean_inc_ref(v_e_980_);
v___x_986_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_980_, v_a_982_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; uint8_t v___x_988_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
v___x_988_ = lean_unbox(v_a_987_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec_ref_known(v___x_986_, 1);
v___x_989_ = l_Lean_Nat_mkInstHMul;
v___x_990_ = l_Lean_Meta_isDefEqI(v_e_980_, v___x_989_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
return v___x_990_;
}
else
{
lean_dec_ref(v_e_980_);
return v___x_986_;
}
}
else
{
lean_dec_ref(v_e_980_);
return v___x_986_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstHMulNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_980_ = stack[0].m_obj;
lean_object* v_a_981_ = stack[1].m_obj;
lean_object* v_a_982_ = stack[2].m_obj;
lean_object* v_a_983_ = stack[3].m_obj;
lean_object* v_a_984_ = stack[4].m_obj;
lean_object* v_res_991_;
v_res_991_ = l_Lean_Meta_DefEq_isInstHMulNat(v_e_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_);
stack->m_obj
 = v_res_991_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulNat___boxed(lean_object* v_e_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Meta_DefEq_isInstHMulNat(v_e_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
return v_res_998_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstLTNat(lean_object* v_e_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1005_; 
lean_inc_ref(v_e_999_);
v___x_1005_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_999_, v_a_1001_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; uint8_t v___x_1007_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
v___x_1007_ = lean_unbox(v_a_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
lean_dec_ref_known(v___x_1005_, 1);
v___x_1008_ = l_Lean_Nat_mkInstLT;
v___x_1009_ = l_Lean_Meta_isDefEqI(v_e_999_, v___x_1008_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
return v___x_1009_;
}
else
{
lean_dec_ref(v_e_999_);
return v___x_1005_;
}
}
else
{
lean_dec_ref(v_e_999_);
return v___x_1005_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstLTNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_999_ = stack[0].m_obj;
lean_object* v_a_1000_ = stack[1].m_obj;
lean_object* v_a_1001_ = stack[2].m_obj;
lean_object* v_a_1002_ = stack[3].m_obj;
lean_object* v_a_1003_ = stack[4].m_obj;
lean_object* v_res_1010_;
v_res_1010_ = l_Lean_Meta_DefEq_isInstLTNat(v_e_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
stack->m_obj
 = v_res_1010_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTNat___boxed(lean_object* v_e_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Meta_DefEq_isInstLTNat(v_e_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec_ref(v_a_1012_);
return v_res_1017_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstLENat(lean_object* v_e_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1024_; 
lean_inc_ref(v_e_1018_);
v___x_1024_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_1018_, v_a_1020_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; uint8_t v___x_1026_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v___x_1026_ = lean_unbox(v_a_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec_ref_known(v___x_1024_, 1);
v___x_1027_ = l_Lean_Nat_mkInstLE;
v___x_1028_ = l_Lean_Meta_isDefEqI(v_e_1018_, v___x_1027_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
return v___x_1028_;
}
else
{
lean_dec_ref(v_e_1018_);
return v___x_1024_;
}
}
else
{
lean_dec_ref(v_e_1018_);
return v___x_1024_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstLENat_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1018_ = stack[0].m_obj;
lean_object* v_a_1019_ = stack[1].m_obj;
lean_object* v_a_1020_ = stack[2].m_obj;
lean_object* v_a_1021_ = stack[3].m_obj;
lean_object* v_a_1022_ = stack[4].m_obj;
lean_object* v_res_1029_;
v_res_1029_ = l_Lean_Meta_DefEq_isInstLENat(v_e_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
stack->m_obj
 = v_res_1029_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLENat___boxed(lean_object* v_e_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_Meta_DefEq_isInstLENat(v_e_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
return v_res_1036_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_NatInstTesters(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_NatInstTesters(builtin);
}
#ifdef __cplusplus
}
#endif
