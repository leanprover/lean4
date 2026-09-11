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
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg(lean_object* v_e_4_, lean_object* v_a_5_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatNat___redArg___boxed(lean_object* v_e_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_e_34_, v_a_35_);
lean_dec(v_a_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatNat(lean_object* v_e_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_Structural_isInstOfNatNat___redArg(v_e_38_, v_a_40_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatNat___boxed(lean_object* v_e_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Meta_Structural_isInstOfNatNat(v_e_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddNat___redArg(lean_object* v_e_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_55_, v_a_56_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_70_; 
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_70_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_70_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_70_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_70_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v___x_64_; uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_68_; 
v___x_63_ = l_Lean_Expr_cleanupAnnotations(v_a_59_);
v___x_64_ = ((lean_object*)(l_Lean_Meta_Structural_isInstAddNat___redArg___closed__1));
v___x_65_ = l_Lean_Expr_isConstOf(v___x_63_, v___x_64_);
lean_dec_ref(v___x_63_);
v___x_66_ = lean_box(v___x_65_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_66_);
v___x_68_ = v___x_61_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_69_; 
v_reuseFailAlloc_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_69_, 0, v___x_66_);
v___x_68_ = v_reuseFailAlloc_69_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
return v___x_68_;
}
}
}
else
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
v_a_71_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v___x_58_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_58_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_71_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddNat___redArg___boxed(lean_object* v_e_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_79_, v_a_80_);
lean_dec(v_a_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddNat(lean_object* v_e_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_83_, v_a_85_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddNat___boxed(lean_object* v_e_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_Structural_isInstAddNat(v_e_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubNat___redArg(lean_object* v_e_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_100_, v_a_101_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_115_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_115_ == 0)
{
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_115_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_115_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_108_ = l_Lean_Expr_cleanupAnnotations(v_a_104_);
v___x_109_ = ((lean_object*)(l_Lean_Meta_Structural_isInstSubNat___redArg___closed__1));
v___x_110_ = l_Lean_Expr_isConstOf(v___x_108_, v___x_109_);
lean_dec_ref(v___x_108_);
v___x_111_ = lean_box(v___x_110_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_111_);
v___x_113_ = v___x_106_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
else
{
lean_object* v_a_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_123_; 
v_a_116_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_123_ == 0)
{
v___x_118_ = v___x_103_;
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_a_116_);
lean_dec(v___x_103_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_123_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v___x_121_; 
if (v_isShared_119_ == 0)
{
v___x_121_ = v___x_118_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_a_116_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubNat___redArg___boxed(lean_object* v_e_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_e_124_, v_a_125_);
lean_dec(v_a_125_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubNat(lean_object* v_e_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_e_128_, v_a_130_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubNat___boxed(lean_object* v_e_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Meta_Structural_isInstSubNat(v_e_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulNat___redArg(lean_object* v_e_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_145_, v_a_146_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_160_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_160_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_160_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_153_ = l_Lean_Expr_cleanupAnnotations(v_a_149_);
v___x_154_ = ((lean_object*)(l_Lean_Meta_Structural_isInstMulNat___redArg___closed__1));
v___x_155_ = l_Lean_Expr_isConstOf(v___x_153_, v___x_154_);
lean_dec_ref(v___x_153_);
v___x_156_ = lean_box(v___x_155_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_156_);
v___x_158_ = v___x_151_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_156_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
v_a_161_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_148_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_148_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulNat___redArg___boxed(lean_object* v_e_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_169_, v_a_170_);
lean_dec(v_a_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulNat(lean_object* v_e_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_173_, v_a_175_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulNat___boxed(lean_object* v_e_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Meta_Structural_isInstMulNat(v_e_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
lean_dec(v_a_182_);
lean_dec_ref(v_a_181_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg(lean_object* v_e_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_192_, v_a_193_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_207_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_207_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_207_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_207_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_200_ = l_Lean_Expr_cleanupAnnotations(v_a_196_);
v___x_201_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDivNat___redArg___closed__2));
v___x_202_ = l_Lean_Expr_isConstOf(v___x_200_, v___x_201_);
lean_dec_ref(v___x_200_);
v___x_203_ = lean_box(v___x_202_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_203_);
v___x_205_ = v___x_198_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_203_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
v_a_208_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_195_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_195_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivNat___redArg___boxed(lean_object* v_e_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_e_216_, v_a_217_);
lean_dec(v_a_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivNat(lean_object* v_e_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_e_220_, v_a_222_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivNat___boxed(lean_object* v_e_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Meta_Structural_isInstDivNat(v_e_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModNat___redArg(lean_object* v_e_238_, lean_object* v_a_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_238_, v_a_239_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_253_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_253_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_253_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_253_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
v___x_246_ = l_Lean_Expr_cleanupAnnotations(v_a_242_);
v___x_247_ = ((lean_object*)(l_Lean_Meta_Structural_isInstModNat___redArg___closed__1));
v___x_248_ = l_Lean_Expr_isConstOf(v___x_246_, v___x_247_);
lean_dec_ref(v___x_246_);
v___x_249_ = lean_box(v___x_248_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_249_);
v___x_251_ = v___x_244_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_249_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
else
{
lean_object* v_a_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_261_; 
v_a_254_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_261_ == 0)
{
v___x_256_ = v___x_241_;
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_a_254_);
lean_dec(v___x_241_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_261_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_259_; 
if (v_isShared_257_ == 0)
{
v___x_259_ = v___x_256_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_a_254_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModNat___redArg___boxed(lean_object* v_e_262_, lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_e_262_, v_a_263_);
lean_dec(v_a_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModNat(lean_object* v_e_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_e_266_, v_a_268_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModNat___boxed(lean_object* v_e_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_Structural_isInstModNat(v_e_273_, v_a_274_, v_a_275_, v_a_276_, v_a_277_);
lean_dec(v_a_277_);
lean_dec_ref(v_a_276_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowNat___redArg(lean_object* v_e_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_283_, v_a_284_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_298_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_298_ == 0)
{
v___x_289_ = v___x_286_;
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_298_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v___x_291_ = l_Lean_Expr_cleanupAnnotations(v_a_287_);
v___x_292_ = ((lean_object*)(l_Lean_Meta_Structural_isInstNatPowNat___redArg___closed__1));
v___x_293_ = l_Lean_Expr_isConstOf(v___x_291_, v___x_292_);
lean_dec_ref(v___x_291_);
v___x_294_ = lean_box(v___x_293_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_294_);
v___x_296_ = v___x_289_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
lean_object* v_a_299_; lean_object* v___x_301_; uint8_t v_isShared_302_; uint8_t v_isSharedCheck_306_; 
v_a_299_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_306_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_306_ == 0)
{
v___x_301_ = v___x_286_;
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
else
{
lean_inc(v_a_299_);
lean_dec(v___x_286_);
v___x_301_ = lean_box(0);
v_isShared_302_ = v_isSharedCheck_306_;
goto v_resetjp_300_;
}
v_resetjp_300_:
{
lean_object* v___x_304_; 
if (v_isShared_302_ == 0)
{
v___x_304_ = v___x_301_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_a_299_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowNat___redArg___boxed(lean_object* v_e_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_e_307_, v_a_308_);
lean_dec(v_a_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowNat(lean_object* v_e_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_e_311_, v_a_313_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowNat___boxed(lean_object* v_e_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Meta_Structural_isInstNatPowNat(v_e_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg(lean_object* v_e_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_328_, v_a_329_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
v___x_337_ = l_Lean_Expr_cleanupAnnotations(v_a_336_);
v___x_338_ = l_Lean_Expr_isApp(v___x_337_);
if (v___x_338_ == 0)
{
lean_dec_ref(v___x_337_);
goto v___jp_331_;
}
else
{
lean_object* v_arg_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_arg_339_ = lean_ctor_get(v___x_337_, 1);
lean_inc_ref(v_arg_339_);
v___x_340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_337_);
v___x_341_ = l_Lean_Expr_isApp(v___x_340_);
if (v___x_341_ == 0)
{
lean_dec_ref(v___x_340_);
lean_dec_ref(v_arg_339_);
goto v___jp_331_;
}
else
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_342_ = l_Lean_Expr_appFnCleanup___redArg(v___x_340_);
v___x_343_ = ((lean_object*)(l_Lean_Meta_Structural_isInstPowNat___redArg___closed__1));
v___x_344_ = l_Lean_Expr_isConstOf(v___x_342_, v___x_343_);
lean_dec_ref(v___x_342_);
if (v___x_344_ == 0)
{
lean_dec_ref(v_arg_339_);
goto v___jp_331_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_arg_339_, v_a_329_);
return v___x_345_;
}
}
}
}
else
{
lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_353_; 
v_a_346_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_353_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_353_ == 0)
{
v___x_348_ = v___x_335_;
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_dec(v___x_335_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_353_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_349_ == 0)
{
v___x_351_ = v___x_348_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_346_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
return v___x_351_;
}
}
}
v___jp_331_:
{
uint8_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = 0;
v___x_333_ = lean_box(v___x_332_);
v___x_334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg___boxed(lean_object* v_e_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_e_354_, v_a_355_);
lean_dec(v_a_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat(lean_object* v_e_358_, lean_object* v_a_359_, lean_object* v_a_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_e_358_, v_a_360_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat___boxed(lean_object* v_e_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Meta_Structural_isInstPowNat(v_e_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object* v_e_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_375_, v_a_376_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
v___x_384_ = l_Lean_Expr_cleanupAnnotations(v_a_383_);
v___x_385_ = l_Lean_Expr_isApp(v___x_384_);
if (v___x_385_ == 0)
{
lean_dec_ref(v___x_384_);
goto v___jp_378_;
}
else
{
lean_object* v_arg_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_arg_386_ = lean_ctor_get(v___x_384_, 1);
lean_inc_ref(v_arg_386_);
v___x_387_ = l_Lean_Expr_appFnCleanup___redArg(v___x_384_);
v___x_388_ = l_Lean_Expr_isApp(v___x_387_);
if (v___x_388_ == 0)
{
lean_dec_ref(v___x_387_);
lean_dec_ref(v_arg_386_);
goto v___jp_378_;
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = l_Lean_Expr_appFnCleanup___redArg(v___x_387_);
v___x_390_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__1));
v___x_391_ = l_Lean_Expr_isConstOf(v___x_389_, v___x_390_);
lean_dec_ref(v___x_389_);
if (v___x_391_ == 0)
{
lean_dec_ref(v_arg_386_);
goto v___jp_378_;
}
else
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_arg_386_, v_a_376_);
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_a_393_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_382_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_382_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
v___jp_378_:
{
uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_379_ = 0;
v___x_380_ = lean_box(v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg___boxed(lean_object* v_e_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_401_, v_a_402_);
lean_dec(v_a_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat(lean_object* v_e_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_405_, v_a_407_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___boxed(lean_object* v_e_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Meta_Structural_isInstHAddNat(v_e_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg(lean_object* v_e_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_422_, v_a_423_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref_known(v___x_429_, 1);
v___x_431_ = l_Lean_Expr_cleanupAnnotations(v_a_430_);
v___x_432_ = l_Lean_Expr_isApp(v___x_431_);
if (v___x_432_ == 0)
{
lean_dec_ref(v___x_431_);
goto v___jp_425_;
}
else
{
lean_object* v_arg_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_arg_433_ = lean_ctor_get(v___x_431_, 1);
lean_inc_ref(v_arg_433_);
v___x_434_ = l_Lean_Expr_appFnCleanup___redArg(v___x_431_);
v___x_435_ = l_Lean_Expr_isApp(v___x_434_);
if (v___x_435_ == 0)
{
lean_dec_ref(v___x_434_);
lean_dec_ref(v_arg_433_);
goto v___jp_425_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_436_ = l_Lean_Expr_appFnCleanup___redArg(v___x_434_);
v___x_437_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__1));
v___x_438_ = l_Lean_Expr_isConstOf(v___x_436_, v___x_437_);
lean_dec_ref(v___x_436_);
if (v___x_438_ == 0)
{
lean_dec_ref(v_arg_433_);
goto v___jp_425_;
}
else
{
lean_object* v___x_439_; 
v___x_439_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_arg_433_, v_a_423_);
return v___x_439_;
}
}
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_447_; 
v_a_440_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_447_ == 0)
{
v___x_442_ = v___x_429_;
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_429_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_447_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_445_; 
if (v_isShared_443_ == 0)
{
v___x_445_ = v___x_442_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_a_440_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
}
v___jp_425_:
{
uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = 0;
v___x_427_ = lean_box(v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg___boxed(lean_object* v_e_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_e_448_, v_a_449_);
lean_dec(v_a_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat(lean_object* v_e_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_e_452_, v_a_454_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___boxed(lean_object* v_e_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Meta_Structural_isInstHSubNat(v_e_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object* v_e_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_469_, v_a_470_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
lean_dec_ref_known(v___x_476_, 1);
v___x_478_ = l_Lean_Expr_cleanupAnnotations(v_a_477_);
v___x_479_ = l_Lean_Expr_isApp(v___x_478_);
if (v___x_479_ == 0)
{
lean_dec_ref(v___x_478_);
goto v___jp_472_;
}
else
{
lean_object* v_arg_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v_arg_480_ = lean_ctor_get(v___x_478_, 1);
lean_inc_ref(v_arg_480_);
v___x_481_ = l_Lean_Expr_appFnCleanup___redArg(v___x_478_);
v___x_482_ = l_Lean_Expr_isApp(v___x_481_);
if (v___x_482_ == 0)
{
lean_dec_ref(v___x_481_);
lean_dec_ref(v_arg_480_);
goto v___jp_472_;
}
else
{
lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_483_ = l_Lean_Expr_appFnCleanup___redArg(v___x_481_);
v___x_484_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__1));
v___x_485_ = l_Lean_Expr_isConstOf(v___x_483_, v___x_484_);
lean_dec_ref(v___x_483_);
if (v___x_485_ == 0)
{
lean_dec_ref(v_arg_480_);
goto v___jp_472_;
}
else
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_arg_480_, v_a_470_);
return v___x_486_;
}
}
}
}
else
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_494_; 
v_a_487_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_494_ == 0)
{
v___x_489_ = v___x_476_;
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_476_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_494_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_492_; 
if (v_isShared_490_ == 0)
{
v___x_492_ = v___x_489_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_493_; 
v_reuseFailAlloc_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_493_, 0, v_a_487_);
v___x_492_ = v_reuseFailAlloc_493_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
return v___x_492_;
}
}
}
v___jp_472_:
{
uint8_t v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = 0;
v___x_474_ = lean_box(v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg___boxed(lean_object* v_e_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_495_, v_a_496_);
lean_dec(v_a_496_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat(lean_object* v_e_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_499_, v_a_501_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___boxed(lean_object* v_e_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_Meta_Structural_isInstHMulNat(v_e_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object* v_e_516_, lean_object* v_a_517_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_516_, v_a_517_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
lean_dec_ref_known(v___x_523_, 1);
v___x_525_ = l_Lean_Expr_cleanupAnnotations(v_a_524_);
v___x_526_ = l_Lean_Expr_isApp(v___x_525_);
if (v___x_526_ == 0)
{
lean_dec_ref(v___x_525_);
goto v___jp_519_;
}
else
{
lean_object* v_arg_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_arg_527_ = lean_ctor_get(v___x_525_, 1);
lean_inc_ref(v_arg_527_);
v___x_528_ = l_Lean_Expr_appFnCleanup___redArg(v___x_525_);
v___x_529_ = l_Lean_Expr_isApp(v___x_528_);
if (v___x_529_ == 0)
{
lean_dec_ref(v___x_528_);
lean_dec_ref(v_arg_527_);
goto v___jp_519_;
}
else
{
lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_530_ = l_Lean_Expr_appFnCleanup___redArg(v___x_528_);
v___x_531_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__1));
v___x_532_ = l_Lean_Expr_isConstOf(v___x_530_, v___x_531_);
lean_dec_ref(v___x_530_);
if (v___x_532_ == 0)
{
lean_dec_ref(v_arg_527_);
goto v___jp_519_;
}
else
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_arg_527_, v_a_517_);
return v___x_533_;
}
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___x_523_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_523_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_523_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
v___jp_519_:
{
uint8_t v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_520_ = 0;
v___x_521_ = lean_box(v___x_520_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg___boxed(lean_object* v_e_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_e_542_, v_a_543_);
lean_dec(v_a_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat(lean_object* v_e_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_e_546_, v_a_548_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___boxed(lean_object* v_e_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Meta_Structural_isInstHDivNat(v_e_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object* v_e_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_563_, v_a_564_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v___x_572_ = l_Lean_Expr_cleanupAnnotations(v_a_571_);
v___x_573_ = l_Lean_Expr_isApp(v___x_572_);
if (v___x_573_ == 0)
{
lean_dec_ref(v___x_572_);
goto v___jp_566_;
}
else
{
lean_object* v_arg_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v_arg_574_ = lean_ctor_get(v___x_572_, 1);
lean_inc_ref(v_arg_574_);
v___x_575_ = l_Lean_Expr_appFnCleanup___redArg(v___x_572_);
v___x_576_ = l_Lean_Expr_isApp(v___x_575_);
if (v___x_576_ == 0)
{
lean_dec_ref(v___x_575_);
lean_dec_ref(v_arg_574_);
goto v___jp_566_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_577_ = l_Lean_Expr_appFnCleanup___redArg(v___x_575_);
v___x_578_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHModNat___redArg___closed__1));
v___x_579_ = l_Lean_Expr_isConstOf(v___x_577_, v___x_578_);
lean_dec_ref(v___x_577_);
if (v___x_579_ == 0)
{
lean_dec_ref(v_arg_574_);
goto v___jp_566_;
}
else
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_arg_574_, v_a_564_);
return v___x_580_;
}
}
}
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
v_a_581_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_570_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_570_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
v___jp_566_:
{
uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = 0;
v___x_568_ = lean_box(v___x_567_);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg___boxed(lean_object* v_e_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_e_589_, v_a_590_);
lean_dec(v_a_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat(lean_object* v_e_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_e_593_, v_a_595_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___boxed(lean_object* v_e_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Meta_Structural_isInstHModNat(v_e_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
lean_dec(v_a_604_);
lean_dec_ref(v_a_603_);
lean_dec(v_a_602_);
lean_dec_ref(v_a_601_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object* v_e_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_610_, v_a_611_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v_a_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_a_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_a_618_);
lean_dec_ref_known(v___x_617_, 1);
v___x_619_ = l_Lean_Expr_cleanupAnnotations(v_a_618_);
v___x_620_ = l_Lean_Expr_isApp(v___x_619_);
if (v___x_620_ == 0)
{
lean_dec_ref(v___x_619_);
goto v___jp_613_;
}
else
{
lean_object* v_arg_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_arg_621_ = lean_ctor_get(v___x_619_, 1);
lean_inc_ref(v_arg_621_);
v___x_622_ = l_Lean_Expr_appFnCleanup___redArg(v___x_619_);
v___x_623_ = l_Lean_Expr_isApp(v___x_622_);
if (v___x_623_ == 0)
{
lean_dec_ref(v___x_622_);
lean_dec_ref(v_arg_621_);
goto v___jp_613_;
}
else
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = l_Lean_Expr_appFnCleanup___redArg(v___x_622_);
v___x_625_ = l_Lean_Expr_isApp(v___x_624_);
if (v___x_625_ == 0)
{
lean_dec_ref(v___x_624_);
lean_dec_ref(v_arg_621_);
goto v___jp_613_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = l_Lean_Expr_appFnCleanup___redArg(v___x_624_);
v___x_627_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__1));
v___x_628_ = l_Lean_Expr_isConstOf(v___x_626_, v___x_627_);
lean_dec_ref(v___x_626_);
if (v___x_628_ == 0)
{
lean_dec_ref(v_arg_621_);
goto v___jp_613_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_arg_621_, v_a_611_);
return v___x_629_;
}
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
v_a_630_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_617_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_617_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
v___jp_613_:
{
uint8_t v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = 0;
v___x_615_ = lean_box(v___x_614_);
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
return v___x_616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg___boxed(lean_object* v_e_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_e_638_, v_a_639_);
lean_dec(v_a_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat(lean_object* v_e_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_e_642_, v_a_644_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___boxed(lean_object* v_e_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_Meta_Structural_isInstHPowNat(v_e_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___redArg(lean_object* v_e_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_659_, v_a_660_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_674_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_674_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_674_ == 0)
{
v___x_665_ = v___x_662_;
v_isShared_666_ = v_isSharedCheck_674_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_662_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_674_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_672_; 
v___x_667_ = l_Lean_Expr_cleanupAnnotations(v_a_663_);
v___x_668_ = ((lean_object*)(l_Lean_Meta_Structural_isInstLTNat___redArg___closed__1));
v___x_669_ = l_Lean_Expr_isConstOf(v___x_667_, v___x_668_);
lean_dec_ref(v___x_667_);
v___x_670_ = lean_box(v___x_669_);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_670_);
v___x_672_ = v___x_665_;
goto v_reusejp_671_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
v___x_672_ = v_reuseFailAlloc_673_;
goto v_reusejp_671_;
}
v_reusejp_671_:
{
return v___x_672_;
}
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
v_a_675_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_662_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_662_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___redArg___boxed(lean_object* v_e_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_683_, v_a_684_);
lean_dec(v_a_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat(lean_object* v_e_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_687_, v_a_689_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___boxed(lean_object* v_e_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lean_Meta_Structural_isInstLTNat(v_e_694_, v_a_695_, v_a_696_, v_a_697_, v_a_698_);
lean_dec(v_a_698_);
lean_dec_ref(v_a_697_);
lean_dec(v_a_696_);
lean_dec_ref(v_a_695_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___redArg(lean_object* v_e_704_, lean_object* v_a_705_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_704_, v_a_705_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_719_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_719_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_719_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_719_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_712_ = l_Lean_Expr_cleanupAnnotations(v_a_708_);
v___x_713_ = ((lean_object*)(l_Lean_Meta_Structural_isInstLENat___redArg___closed__1));
v___x_714_ = l_Lean_Expr_isConstOf(v___x_712_, v___x_713_);
lean_dec_ref(v___x_712_);
v___x_715_ = lean_box(v___x_714_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_715_);
v___x_717_ = v___x_710_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
v_a_720_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_707_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_707_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___redArg___boxed(lean_object* v_e_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_728_, v_a_729_);
lean_dec(v_a_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat(lean_object* v_e_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_732_, v_a_734_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___boxed(lean_object* v_e_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_Meta_Structural_isInstLENat(v_e_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg(lean_object* v_e_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_750_, v_a_751_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_765_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_765_ == 0)
{
v___x_756_ = v___x_753_;
v_isShared_757_ = v_isSharedCheck_765_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_753_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_765_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_758_ = l_Lean_Expr_cleanupAnnotations(v_a_754_);
v___x_759_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1));
v___x_760_ = l_Lean_Expr_isConstOf(v___x_758_, v___x_759_);
lean_dec_ref(v___x_758_);
v___x_761_ = lean_box(v___x_760_);
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 0, v___x_761_);
v___x_763_ = v___x_756_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
v_a_766_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_753_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_753_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg___boxed(lean_object* v_e_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_e_774_, v_a_775_);
lean_dec(v_a_775_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat(lean_object* v_e_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_e_778_, v_a_780_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___boxed(lean_object* v_e_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_Structural_isInstDvdNat(v_e_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddNat(lean_object* v_e_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v___x_798_; 
lean_inc_ref(v_e_792_);
v___x_798_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_792_, v_a_794_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; uint8_t v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
v___x_800_ = lean_unbox(v_a_799_);
lean_dec(v_a_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref_known(v___x_798_, 1);
v___x_801_ = l_Lean_Nat_mkInstAdd;
v___x_802_ = l_Lean_Meta_isDefEqI(v_e_792_, v___x_801_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
return v___x_802_;
}
else
{
lean_dec_ref(v_e_792_);
return v___x_798_;
}
}
else
{
lean_dec_ref(v_e_792_);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddNat___boxed(lean_object* v_e_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Meta_DefEq_isInstAddNat(v_e_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddNat(lean_object* v_e_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v___x_816_; 
lean_inc_ref(v_e_810_);
v___x_816_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_810_, v_a_812_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; uint8_t v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
v___x_818_ = lean_unbox(v_a_817_);
lean_dec(v_a_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
lean_dec_ref_known(v___x_816_, 1);
v___x_819_ = l_Lean_Nat_mkInstHAdd;
v___x_820_ = l_Lean_Meta_isDefEqI(v_e_810_, v___x_819_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
return v___x_820_;
}
else
{
lean_dec_ref(v_e_810_);
return v___x_816_;
}
}
else
{
lean_dec_ref(v_e_810_);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddNat___boxed(lean_object* v_e_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Meta_DefEq_isInstHAddNat(v_e_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulNat(lean_object* v_e_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; 
lean_inc_ref(v_e_828_);
v___x_834_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_828_, v_a_830_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; uint8_t v___x_836_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_835_);
v___x_836_ = lean_unbox(v_a_835_);
lean_dec(v_a_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_838_; 
lean_dec_ref_known(v___x_834_, 1);
v___x_837_ = l_Lean_Nat_mkInstMul;
v___x_838_ = l_Lean_Meta_isDefEqI(v_e_828_, v___x_837_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
return v___x_838_;
}
else
{
lean_dec_ref(v_e_828_);
return v___x_834_;
}
}
else
{
lean_dec_ref(v_e_828_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulNat___boxed(lean_object* v_e_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Meta_DefEq_isInstMulNat(v_e_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulNat(lean_object* v_e_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v___x_852_; 
lean_inc_ref(v_e_846_);
v___x_852_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_846_, v_a_848_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; uint8_t v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
v___x_854_ = lean_unbox(v_a_853_);
lean_dec(v_a_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec_ref_known(v___x_852_, 1);
v___x_855_ = l_Lean_Nat_mkInstHMul;
v___x_856_ = l_Lean_Meta_isDefEqI(v_e_846_, v___x_855_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
return v___x_856_;
}
else
{
lean_dec_ref(v_e_846_);
return v___x_852_;
}
}
else
{
lean_dec_ref(v_e_846_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulNat___boxed(lean_object* v_e_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Meta_DefEq_isInstHMulNat(v_e_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTNat(lean_object* v_e_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___x_870_; 
lean_inc_ref(v_e_864_);
v___x_870_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_864_, v_a_866_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; uint8_t v___x_872_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
v___x_872_ = lean_unbox(v_a_871_);
lean_dec(v_a_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec_ref_known(v___x_870_, 1);
v___x_873_ = l_Lean_Nat_mkInstLT;
v___x_874_ = l_Lean_Meta_isDefEqI(v_e_864_, v___x_873_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
return v___x_874_;
}
else
{
lean_dec_ref(v_e_864_);
return v___x_870_;
}
}
else
{
lean_dec_ref(v_e_864_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTNat___boxed(lean_object* v_e_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Meta_DefEq_isInstLTNat(v_e_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLENat(lean_object* v_e_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v___x_888_; 
lean_inc_ref(v_e_882_);
v___x_888_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_882_, v_a_884_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; uint8_t v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
v___x_890_ = lean_unbox(v_a_889_);
lean_dec(v_a_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec_ref_known(v___x_888_, 1);
v___x_891_ = l_Lean_Nat_mkInstLE;
v___x_892_ = l_Lean_Meta_isDefEqI(v_e_882_, v___x_891_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
return v___x_892_;
}
else
{
lean_dec_ref(v_e_882_);
return v___x_888_;
}
}
else
{
lean_dec_ref(v_e_882_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLENat___boxed(lean_object* v_e_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Meta_DefEq_isInstLENat(v_e_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
return v_res_899_;
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
