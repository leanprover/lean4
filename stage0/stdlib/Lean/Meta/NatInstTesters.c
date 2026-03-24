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
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4_, v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_25_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_25_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_25_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_25_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_18_ = l_Lean_Expr_cleanupAnnotations(v_a_8_);
v___x_19_ = l_Lean_Expr_isApp(v___x_18_);
if (v___x_19_ == 0)
{
lean_dec_ref(v___x_18_);
goto v___jp_12_;
}
else
{
lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_20_ = l_Lean_Expr_appFnCleanup___redArg(v___x_18_);
v___x_21_ = ((lean_object*)(l_Lean_Meta_Structural_isInstOfNatNat___redArg___closed__1));
v___x_22_ = l_Lean_Expr_isConstOf(v___x_20_, v___x_21_);
lean_dec_ref(v___x_20_);
if (v___x_22_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_del_object(v___x_10_);
v___x_23_ = lean_box(v___x_22_);
v___x_24_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
return v___x_24_;
}
}
v___jp_12_:
{
uint8_t v___x_13_; lean_object* v___x_14_; lean_object* v___x_16_; 
v___x_13_ = 0;
v___x_14_ = lean_box(v___x_13_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_14_);
v___x_16_ = v___x_10_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
else
{
lean_object* v_a_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_33_; 
v_a_26_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_33_ == 0)
{
v___x_28_ = v___x_7_;
v_isShared_29_ = v_isSharedCheck_33_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_a_26_);
lean_dec(v___x_7_);
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
lean_object* v___x_331_; 
v___x_331_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_328_, v_a_329_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_351_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_351_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_351_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_351_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = l_Lean_Expr_cleanupAnnotations(v_a_332_);
v___x_343_ = l_Lean_Expr_isApp(v___x_342_);
if (v___x_343_ == 0)
{
lean_dec_ref(v___x_342_);
goto v___jp_336_;
}
else
{
lean_object* v_arg_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_arg_344_ = lean_ctor_get(v___x_342_, 1);
lean_inc_ref(v_arg_344_);
v___x_345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_342_);
v___x_346_ = l_Lean_Expr_isApp(v___x_345_);
if (v___x_346_ == 0)
{
lean_dec_ref(v___x_345_);
lean_dec_ref(v_arg_344_);
goto v___jp_336_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_345_);
v___x_348_ = ((lean_object*)(l_Lean_Meta_Structural_isInstPowNat___redArg___closed__1));
v___x_349_ = l_Lean_Expr_isConstOf(v___x_347_, v___x_348_);
lean_dec_ref(v___x_347_);
if (v___x_349_ == 0)
{
lean_dec_ref(v_arg_344_);
goto v___jp_336_;
}
else
{
lean_object* v___x_350_; 
lean_del_object(v___x_334_);
v___x_350_ = l_Lean_Meta_Structural_isInstNatPowNat___redArg(v_arg_344_, v_a_329_);
return v___x_350_;
}
}
}
v___jp_336_:
{
uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_337_ = 0;
v___x_338_ = lean_box(v___x_337_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_338_);
v___x_340_ = v___x_334_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_331_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_331_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat___redArg___boxed(lean_object* v_e_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_e_360_, v_a_361_);
lean_dec(v_a_361_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat(lean_object* v_e_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_e_364_, v_a_366_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowNat___boxed(lean_object* v_e_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_Structural_isInstPowNat(v_e_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object* v_e_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___x_384_; 
v___x_384_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_381_, v_a_382_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_404_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_404_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_404_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_404_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = l_Lean_Expr_cleanupAnnotations(v_a_385_);
v___x_396_ = l_Lean_Expr_isApp(v___x_395_);
if (v___x_396_ == 0)
{
lean_dec_ref(v___x_395_);
goto v___jp_389_;
}
else
{
lean_object* v_arg_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_arg_397_ = lean_ctor_get(v___x_395_, 1);
lean_inc_ref(v_arg_397_);
v___x_398_ = l_Lean_Expr_appFnCleanup___redArg(v___x_395_);
v___x_399_ = l_Lean_Expr_isApp(v___x_398_);
if (v___x_399_ == 0)
{
lean_dec_ref(v___x_398_);
lean_dec_ref(v_arg_397_);
goto v___jp_389_;
}
else
{
lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_400_ = l_Lean_Expr_appFnCleanup___redArg(v___x_398_);
v___x_401_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHAddNat___redArg___closed__1));
v___x_402_ = l_Lean_Expr_isConstOf(v___x_400_, v___x_401_);
lean_dec_ref(v___x_400_);
if (v___x_402_ == 0)
{
lean_dec_ref(v_arg_397_);
goto v___jp_389_;
}
else
{
lean_object* v___x_403_; 
lean_del_object(v___x_387_);
v___x_403_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_arg_397_, v_a_382_);
return v___x_403_;
}
}
}
v___jp_389_:
{
uint8_t v___x_390_; lean_object* v___x_391_; lean_object* v___x_393_; 
v___x_390_ = 0;
v___x_391_ = lean_box(v___x_390_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 0, v___x_391_);
v___x_393_ = v___x_387_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v___x_391_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
v_a_405_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_384_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_384_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg___boxed(lean_object* v_e_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_413_, v_a_414_);
lean_dec(v_a_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat(lean_object* v_e_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_417_, v_a_419_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddNat___boxed(lean_object* v_e_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Meta_Structural_isInstHAddNat(v_e_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
lean_dec(v_a_426_);
lean_dec_ref(v_a_425_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg(lean_object* v_e_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_434_, v_a_435_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_457_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_457_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_457_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_457_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = l_Lean_Expr_cleanupAnnotations(v_a_438_);
v___x_449_ = l_Lean_Expr_isApp(v___x_448_);
if (v___x_449_ == 0)
{
lean_dec_ref(v___x_448_);
goto v___jp_442_;
}
else
{
lean_object* v_arg_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_arg_450_ = lean_ctor_get(v___x_448_, 1);
lean_inc_ref(v_arg_450_);
v___x_451_ = l_Lean_Expr_appFnCleanup___redArg(v___x_448_);
v___x_452_ = l_Lean_Expr_isApp(v___x_451_);
if (v___x_452_ == 0)
{
lean_dec_ref(v___x_451_);
lean_dec_ref(v_arg_450_);
goto v___jp_442_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_453_ = l_Lean_Expr_appFnCleanup___redArg(v___x_451_);
v___x_454_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHSubNat___redArg___closed__1));
v___x_455_ = l_Lean_Expr_isConstOf(v___x_453_, v___x_454_);
lean_dec_ref(v___x_453_);
if (v___x_455_ == 0)
{
lean_dec_ref(v_arg_450_);
goto v___jp_442_;
}
else
{
lean_object* v___x_456_; 
lean_del_object(v___x_440_);
v___x_456_ = l_Lean_Meta_Structural_isInstSubNat___redArg(v_arg_450_, v_a_435_);
return v___x_456_;
}
}
}
v___jp_442_:
{
uint8_t v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_443_ = 0;
v___x_444_ = lean_box(v___x_443_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_444_);
v___x_446_ = v___x_440_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_465_; 
v_a_458_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_465_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_465_ == 0)
{
v___x_460_ = v___x_437_;
v_isShared_461_ = v_isSharedCheck_465_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_437_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg___boxed(lean_object* v_e_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_e_466_, v_a_467_);
lean_dec(v_a_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat(lean_object* v_e_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Meta_Structural_isInstHSubNat___redArg(v_e_470_, v_a_472_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubNat___boxed(lean_object* v_e_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lean_Meta_Structural_isInstHSubNat(v_e_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec(v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec_ref(v_a_478_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object* v_e_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; 
v___x_490_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_487_, v_a_488_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_510_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_510_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_510_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_510_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = l_Lean_Expr_cleanupAnnotations(v_a_491_);
v___x_502_ = l_Lean_Expr_isApp(v___x_501_);
if (v___x_502_ == 0)
{
lean_dec_ref(v___x_501_);
goto v___jp_495_;
}
else
{
lean_object* v_arg_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_arg_503_ = lean_ctor_get(v___x_501_, 1);
lean_inc_ref(v_arg_503_);
v___x_504_ = l_Lean_Expr_appFnCleanup___redArg(v___x_501_);
v___x_505_ = l_Lean_Expr_isApp(v___x_504_);
if (v___x_505_ == 0)
{
lean_dec_ref(v___x_504_);
lean_dec_ref(v_arg_503_);
goto v___jp_495_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v___x_506_ = l_Lean_Expr_appFnCleanup___redArg(v___x_504_);
v___x_507_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHMulNat___redArg___closed__1));
v___x_508_ = l_Lean_Expr_isConstOf(v___x_506_, v___x_507_);
lean_dec_ref(v___x_506_);
if (v___x_508_ == 0)
{
lean_dec_ref(v_arg_503_);
goto v___jp_495_;
}
else
{
lean_object* v___x_509_; 
lean_del_object(v___x_493_);
v___x_509_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_arg_503_, v_a_488_);
return v___x_509_;
}
}
}
v___jp_495_:
{
uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_496_ = 0;
v___x_497_ = lean_box(v___x_496_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_497_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
v_a_511_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_490_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_490_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg___boxed(lean_object* v_e_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_519_, v_a_520_);
lean_dec(v_a_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat(lean_object* v_e_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_523_, v_a_525_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulNat___boxed(lean_object* v_e_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Meta_Structural_isInstHMulNat(v_e_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object* v_e_540_, lean_object* v_a_541_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_540_, v_a_541_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_563_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_563_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_563_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_563_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_554_ = l_Lean_Expr_cleanupAnnotations(v_a_544_);
v___x_555_ = l_Lean_Expr_isApp(v___x_554_);
if (v___x_555_ == 0)
{
lean_dec_ref(v___x_554_);
goto v___jp_548_;
}
else
{
lean_object* v_arg_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_arg_556_ = lean_ctor_get(v___x_554_, 1);
lean_inc_ref(v_arg_556_);
v___x_557_ = l_Lean_Expr_appFnCleanup___redArg(v___x_554_);
v___x_558_ = l_Lean_Expr_isApp(v___x_557_);
if (v___x_558_ == 0)
{
lean_dec_ref(v___x_557_);
lean_dec_ref(v_arg_556_);
goto v___jp_548_;
}
else
{
lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v___x_559_ = l_Lean_Expr_appFnCleanup___redArg(v___x_557_);
v___x_560_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHDivNat___redArg___closed__1));
v___x_561_ = l_Lean_Expr_isConstOf(v___x_559_, v___x_560_);
lean_dec_ref(v___x_559_);
if (v___x_561_ == 0)
{
lean_dec_ref(v_arg_556_);
goto v___jp_548_;
}
else
{
lean_object* v___x_562_; 
lean_del_object(v___x_546_);
v___x_562_ = l_Lean_Meta_Structural_isInstDivNat___redArg(v_arg_556_, v_a_541_);
return v___x_562_;
}
}
}
v___jp_548_:
{
uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_552_; 
v___x_549_ = 0;
v___x_550_ = lean_box(v___x_549_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_550_);
v___x_552_ = v___x_546_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_550_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_571_; 
v_a_564_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_571_ == 0)
{
v___x_566_ = v___x_543_;
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_543_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_571_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_a_564_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg___boxed(lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_e_572_, v_a_573_);
lean_dec(v_a_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat(lean_object* v_e_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Meta_Structural_isInstHDivNat___redArg(v_e_576_, v_a_578_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivNat___boxed(lean_object* v_e_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_Meta_Structural_isInstHDivNat(v_e_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_);
lean_dec(v_a_587_);
lean_dec_ref(v_a_586_);
lean_dec(v_a_585_);
lean_dec_ref(v_a_584_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object* v_e_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_593_, v_a_594_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_616_; 
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_616_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_616_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_616_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = l_Lean_Expr_cleanupAnnotations(v_a_597_);
v___x_608_ = l_Lean_Expr_isApp(v___x_607_);
if (v___x_608_ == 0)
{
lean_dec_ref(v___x_607_);
goto v___jp_601_;
}
else
{
lean_object* v_arg_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_arg_609_ = lean_ctor_get(v___x_607_, 1);
lean_inc_ref(v_arg_609_);
v___x_610_ = l_Lean_Expr_appFnCleanup___redArg(v___x_607_);
v___x_611_ = l_Lean_Expr_isApp(v___x_610_);
if (v___x_611_ == 0)
{
lean_dec_ref(v___x_610_);
lean_dec_ref(v_arg_609_);
goto v___jp_601_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_610_);
v___x_613_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHModNat___redArg___closed__1));
v___x_614_ = l_Lean_Expr_isConstOf(v___x_612_, v___x_613_);
lean_dec_ref(v___x_612_);
if (v___x_614_ == 0)
{
lean_dec_ref(v_arg_609_);
goto v___jp_601_;
}
else
{
lean_object* v___x_615_; 
lean_del_object(v___x_599_);
v___x_615_ = l_Lean_Meta_Structural_isInstModNat___redArg(v_arg_609_, v_a_594_);
return v___x_615_;
}
}
}
v___jp_601_:
{
uint8_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_602_ = 0;
v___x_603_ = lean_box(v___x_602_);
if (v_isShared_600_ == 0)
{
lean_ctor_set(v___x_599_, 0, v___x_603_);
v___x_605_ = v___x_599_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v___x_603_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_a_617_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_596_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_596_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg___boxed(lean_object* v_e_625_, lean_object* v_a_626_, lean_object* v_a_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_e_625_, v_a_626_);
lean_dec(v_a_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat(lean_object* v_e_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Meta_Structural_isInstHModNat___redArg(v_e_629_, v_a_631_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModNat___boxed(lean_object* v_e_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_Meta_Structural_isInstHModNat(v_e_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec(v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec_ref(v_a_637_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object* v_e_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_646_, v_a_647_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_671_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_671_ == 0)
{
v___x_652_ = v___x_649_;
v_isShared_653_ = v_isSharedCheck_671_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_671_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_660_ = l_Lean_Expr_cleanupAnnotations(v_a_650_);
v___x_661_ = l_Lean_Expr_isApp(v___x_660_);
if (v___x_661_ == 0)
{
lean_dec_ref(v___x_660_);
goto v___jp_654_;
}
else
{
lean_object* v_arg_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_arg_662_ = lean_ctor_get(v___x_660_, 1);
lean_inc_ref(v_arg_662_);
v___x_663_ = l_Lean_Expr_appFnCleanup___redArg(v___x_660_);
v___x_664_ = l_Lean_Expr_isApp(v___x_663_);
if (v___x_664_ == 0)
{
lean_dec_ref(v___x_663_);
lean_dec_ref(v_arg_662_);
goto v___jp_654_;
}
else
{
lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_665_ = l_Lean_Expr_appFnCleanup___redArg(v___x_663_);
v___x_666_ = l_Lean_Expr_isApp(v___x_665_);
if (v___x_666_ == 0)
{
lean_dec_ref(v___x_665_);
lean_dec_ref(v_arg_662_);
goto v___jp_654_;
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_667_ = l_Lean_Expr_appFnCleanup___redArg(v___x_665_);
v___x_668_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHPowNat___redArg___closed__1));
v___x_669_ = l_Lean_Expr_isConstOf(v___x_667_, v___x_668_);
lean_dec_ref(v___x_667_);
if (v___x_669_ == 0)
{
lean_dec_ref(v_arg_662_);
goto v___jp_654_;
}
else
{
lean_object* v___x_670_; 
lean_del_object(v___x_652_);
v___x_670_ = l_Lean_Meta_Structural_isInstPowNat___redArg(v_arg_662_, v_a_647_);
return v___x_670_;
}
}
}
}
v___jp_654_:
{
uint8_t v___x_655_; lean_object* v___x_656_; lean_object* v___x_658_; 
v___x_655_ = 0;
v___x_656_ = lean_box(v___x_655_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_656_);
v___x_658_ = v___x_652_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
v_a_672_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_649_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_649_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg___boxed(lean_object* v_e_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_e_680_, v_a_681_);
lean_dec(v_a_681_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat(lean_object* v_e_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_Meta_Structural_isInstHPowNat___redArg(v_e_684_, v_a_686_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowNat___boxed(lean_object* v_e_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Meta_Structural_isInstHPowNat(v_e_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
lean_dec(v_a_693_);
lean_dec_ref(v_a_692_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___redArg(lean_object* v_e_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_701_, v_a_702_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_716_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_716_ == 0)
{
v___x_707_ = v___x_704_;
v_isShared_708_ = v_isSharedCheck_716_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_704_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_716_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_709_ = l_Lean_Expr_cleanupAnnotations(v_a_705_);
v___x_710_ = ((lean_object*)(l_Lean_Meta_Structural_isInstLTNat___redArg___closed__1));
v___x_711_ = l_Lean_Expr_isConstOf(v___x_709_, v___x_710_);
lean_dec_ref(v___x_709_);
v___x_712_ = lean_box(v___x_711_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_712_);
v___x_714_ = v___x_707_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
v_a_717_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_704_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_704_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___redArg___boxed(lean_object* v_e_725_, lean_object* v_a_726_, lean_object* v_a_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_725_, v_a_726_);
lean_dec(v_a_726_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat(lean_object* v_e_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_729_, v_a_731_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTNat___boxed(lean_object* v_e_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Meta_Structural_isInstLTNat(v_e_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___redArg(lean_object* v_e_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_746_, v_a_747_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_761_; 
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_761_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_761_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_761_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_754_ = l_Lean_Expr_cleanupAnnotations(v_a_750_);
v___x_755_ = ((lean_object*)(l_Lean_Meta_Structural_isInstLENat___redArg___closed__1));
v___x_756_ = l_Lean_Expr_isConstOf(v___x_754_, v___x_755_);
lean_dec_ref(v___x_754_);
v___x_757_ = lean_box(v___x_756_);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 0, v___x_757_);
v___x_759_ = v___x_752_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
v_a_762_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_749_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_749_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___redArg___boxed(lean_object* v_e_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_770_, v_a_771_);
lean_dec(v_a_771_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat(lean_object* v_e_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_774_, v_a_776_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLENat___boxed(lean_object* v_e_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_Structural_isInstLENat(v_e_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg(lean_object* v_e_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_792_, v_a_793_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_807_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_807_ == 0)
{
v___x_798_ = v___x_795_;
v_isShared_799_ = v_isSharedCheck_807_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_a_796_);
lean_dec(v___x_795_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_807_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_800_ = l_Lean_Expr_cleanupAnnotations(v_a_796_);
v___x_801_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDvdNat___redArg___closed__1));
v___x_802_ = l_Lean_Expr_isConstOf(v___x_800_, v___x_801_);
lean_dec_ref(v___x_800_);
v___x_803_ = lean_box(v___x_802_);
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 0, v___x_803_);
v___x_805_ = v___x_798_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
v_a_808_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_795_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_795_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg___boxed(lean_object* v_e_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_e_816_, v_a_817_);
lean_dec(v_a_817_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat(lean_object* v_e_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_e_820_, v_a_822_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdNat___boxed(lean_object* v_e_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_Meta_Structural_isInstDvdNat(v_e_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddNat(lean_object* v_e_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; 
lean_inc_ref(v_e_834_);
v___x_840_ = l_Lean_Meta_Structural_isInstAddNat___redArg(v_e_834_, v_a_836_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; uint8_t v___x_842_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_a_841_);
v___x_842_ = lean_unbox(v_a_841_);
lean_dec(v_a_841_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; 
lean_dec_ref(v___x_840_);
v___x_843_ = l_Lean_Nat_mkInstAdd;
v___x_844_ = l_Lean_Meta_isDefEqI(v_e_834_, v___x_843_, v_a_835_, v_a_836_, v_a_837_, v_a_838_);
return v___x_844_;
}
else
{
lean_dec_ref(v_e_834_);
return v___x_840_;
}
}
else
{
lean_dec_ref(v_e_834_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddNat___boxed(lean_object* v_e_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_Meta_DefEq_isInstAddNat(v_e_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddNat(lean_object* v_e_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; 
lean_inc_ref(v_e_852_);
v___x_858_ = l_Lean_Meta_Structural_isInstHAddNat___redArg(v_e_852_, v_a_854_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; uint8_t v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
v___x_860_ = lean_unbox(v_a_859_);
lean_dec(v_a_859_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec_ref(v___x_858_);
v___x_861_ = l_Lean_Nat_mkInstHAdd;
v___x_862_ = l_Lean_Meta_isDefEqI(v_e_852_, v___x_861_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
return v___x_862_;
}
else
{
lean_dec_ref(v_e_852_);
return v___x_858_;
}
}
else
{
lean_dec_ref(v_e_852_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddNat___boxed(lean_object* v_e_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Meta_DefEq_isInstHAddNat(v_e_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulNat(lean_object* v_e_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v___x_876_; 
lean_inc_ref(v_e_870_);
v___x_876_ = l_Lean_Meta_Structural_isInstMulNat___redArg(v_e_870_, v_a_872_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; uint8_t v___x_878_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc(v_a_877_);
v___x_878_ = lean_unbox(v_a_877_);
lean_dec(v_a_877_);
if (v___x_878_ == 0)
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec_ref(v___x_876_);
v___x_879_ = l_Lean_Nat_mkInstMul;
v___x_880_ = l_Lean_Meta_isDefEqI(v_e_870_, v___x_879_, v_a_871_, v_a_872_, v_a_873_, v_a_874_);
return v___x_880_;
}
else
{
lean_dec_ref(v_e_870_);
return v___x_876_;
}
}
else
{
lean_dec_ref(v_e_870_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulNat___boxed(lean_object* v_e_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Meta_DefEq_isInstMulNat(v_e_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulNat(lean_object* v_e_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_894_; 
lean_inc_ref(v_e_888_);
v___x_894_ = l_Lean_Meta_Structural_isInstHMulNat___redArg(v_e_888_, v_a_890_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; uint8_t v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
v___x_896_ = lean_unbox(v_a_895_);
lean_dec(v_a_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec_ref(v___x_894_);
v___x_897_ = l_Lean_Nat_mkInstHMul;
v___x_898_ = l_Lean_Meta_isDefEqI(v_e_888_, v___x_897_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
return v___x_898_;
}
else
{
lean_dec_ref(v_e_888_);
return v___x_894_;
}
}
else
{
lean_dec_ref(v_e_888_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulNat___boxed(lean_object* v_e_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_Meta_DefEq_isInstHMulNat(v_e_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec(v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec_ref(v_a_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTNat(lean_object* v_e_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; 
lean_inc_ref(v_e_906_);
v___x_912_ = l_Lean_Meta_Structural_isInstLTNat___redArg(v_e_906_, v_a_908_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; uint8_t v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
v___x_914_ = lean_unbox(v_a_913_);
lean_dec(v_a_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; 
lean_dec_ref(v___x_912_);
v___x_915_ = l_Lean_Nat_mkInstLT;
v___x_916_ = l_Lean_Meta_isDefEqI(v_e_906_, v___x_915_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
return v___x_916_;
}
else
{
lean_dec_ref(v_e_906_);
return v___x_912_;
}
}
else
{
lean_dec_ref(v_e_906_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTNat___boxed(lean_object* v_e_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_Meta_DefEq_isInstLTNat(v_e_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLENat(lean_object* v_e_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
lean_object* v___x_930_; 
lean_inc_ref(v_e_924_);
v___x_930_ = l_Lean_Meta_Structural_isInstLENat___redArg(v_e_924_, v_a_926_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; uint8_t v___x_932_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
lean_inc(v_a_931_);
v___x_932_ = lean_unbox(v_a_931_);
lean_dec(v_a_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec_ref(v___x_930_);
v___x_933_ = l_Lean_Nat_mkInstLE;
v___x_934_ = l_Lean_Meta_isDefEqI(v_e_924_, v___x_933_, v_a_925_, v_a_926_, v_a_927_, v_a_928_);
return v___x_934_;
}
else
{
lean_dec_ref(v_e_924_);
return v___x_930_;
}
}
else
{
lean_dec_ref(v_e_924_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLENat___boxed(lean_object* v_e_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Lean_Meta_DefEq_isInstLENat(v_e_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
return v_res_941_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
