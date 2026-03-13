// Lean compiler output
// Module: Lean.Meta.IntInstTesters
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
extern lean_object* l_Lean_Int_mkInstHAdd;
lean_object* l_Lean_Meta_isDefEqI(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstHMul;
extern lean_object* l_Lean_Int_mkInstLT;
extern lean_object* l_Lean_Int_mkInstMul;
extern lean_object* l_Lean_Int_mkInstSub;
extern lean_object* l_Lean_Int_mkInstAdd;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_Int_mkInstNeg;
extern lean_object* l_Lean_Int_mkInstLE;
extern lean_object* l_Lean_Int_mkInstHSub;
static const lean_string_object l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 253, 199, 38, 151, 242, 146)}};
static const lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Structural_isInstNegInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNegInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNegInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstAddInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instAdd"};
static const lean_object* l_Lean_Meta_Structural_isInstAddInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstAddInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstAddInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 99, 69, 75, 84, 154, 200, 179)}};
static const lean_object* l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstSubInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instSub"};
static const lean_object* l_Lean_Meta_Structural_isInstSubInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstSubInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstSubInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(28, 85, 79, 77, 38, 86, 116, 189)}};
static const lean_object* l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstMulInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMul"};
static const lean_object* l_Lean_Meta_Structural_isInstMulInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstMulInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstMulInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(101, 121, 189, 72, 180, 169, 35, 121)}};
static const lean_object* l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstDivInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDiv"};
static const lean_object* l_Lean_Meta_Structural_isInstDivInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstDivInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstDivInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 154, 103, 19, 118, 118, 20, 12)}};
static const lean_object* l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstModInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instMod"};
static const lean_object* l_Lean_Meta_Structural_isInstModInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstModInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstModInt___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstModInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstModInt___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstModInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 18, 147, 153, 76, 63, 153, 183)}};
static const lean_object* l_Lean_Meta_Structural_isInstModInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstModInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDvd"};
static const lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 20, 243, 72, 185, 226, 91, 120)}};
static const lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHAdd"};
static const lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 81, 239, 34, 203, 244, 36, 133)}};
static const lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHSub"};
static const lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(32, 225, 92, 14, 170, 61, 170, 140)}};
static const lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMul"};
static const lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 107, 107, 59, 202, 230, 169, 251)}};
static const lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHDiv"};
static const lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 70, 113, 198, 157, 211, 131, 18)}};
static const lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHModInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHMod"};
static const lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHModInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHModInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHModInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 7, 29, 140, 31, 32, 204, 87)}};
static const lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHModInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstLTInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLTInt"};
static const lean_object* l_Lean_Meta_Structural_isInstLTInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstLTInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstLTInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 212, 102, 196, 69, 170, 149, 126)}};
static const lean_object* l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstLEInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instLEInt"};
static const lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstLEInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstLEInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 143, 147, 243, 104, 145, 221, 241)}};
static const lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLEInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLEInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNatPow"};
static const lean_object* l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstNegInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 111, 246, 9, 99, 98, 200, 100)}};
static const lean_object* l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstPowInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instPowNat"};
static const lean_object* l_Lean_Meta_Structural_isInstPowInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstPowInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstPowInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstPowInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(173, 228, 103, 52, 5, 80, 7, 4)}};
static const lean_object* l_Lean_Meta_Structural_isInstPowInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstPowInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHPow"};
static const lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(213, 197, 76, 235, 199, 0, 254, 199)}};
static const lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstNegInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstNegInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstSubInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstSubInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHSubInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHSubInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLEInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLEInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_DefEq_isInstDvdInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DefEq_isInstDvdInt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstDvdInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstDvdInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg(lean_object* v_e_4_, lean_object* v_a_5_){
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
v___x_21_ = ((lean_object*)(l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__1));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg___boxed(lean_object* v_e_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v_e_34_, v_a_35_);
lean_dec(v_a_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatInt(lean_object* v_e_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v_e_38_, v_a_40_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatInt___boxed(lean_object* v_e_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Meta_Structural_isInstOfNatInt(v_e_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object* v_e_57_, lean_object* v_a_58_){
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
v___x_66_ = ((lean_object*)(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2));
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
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg___boxed(lean_object* v_e_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_e_81_, v_a_82_);
lean_dec(v_a_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNegInt(lean_object* v_e_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_e_85_, v_a_87_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNegInt___boxed(lean_object* v_e_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Meta_Structural_isInstNegInt(v_e_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_);
lean_dec(v_a_96_);
lean_dec_ref(v_a_95_);
lean_dec(v_a_94_);
lean_dec_ref(v_a_93_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddInt___redArg(lean_object* v_e_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_103_, v_a_104_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_118_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_118_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_111_ = l_Lean_Expr_cleanupAnnotations(v_a_107_);
v___x_112_ = ((lean_object*)(l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1));
v___x_113_ = l_Lean_Expr_isConstOf(v___x_111_, v___x_112_);
lean_dec_ref(v___x_111_);
v___x_114_ = lean_box(v___x_113_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v___x_114_);
v___x_116_ = v___x_109_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
else
{
lean_object* v_a_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_126_; 
v_a_119_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_126_ == 0)
{
v___x_121_ = v___x_106_;
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_a_119_);
lean_dec(v___x_106_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_126_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_124_; 
if (v_isShared_122_ == 0)
{
v___x_124_ = v___x_121_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_a_119_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddInt___redArg___boxed(lean_object* v_e_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_e_127_, v_a_128_);
lean_dec(v_a_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddInt(lean_object* v_e_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_e_131_, v_a_133_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddInt___boxed(lean_object* v_e_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lean_Meta_Structural_isInstAddInt(v_e_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubInt___redArg(lean_object* v_e_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_149_, v_a_150_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_164_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_164_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_164_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_164_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_157_ = l_Lean_Expr_cleanupAnnotations(v_a_153_);
v___x_158_ = ((lean_object*)(l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1));
v___x_159_ = l_Lean_Expr_isConstOf(v___x_157_, v___x_158_);
lean_dec_ref(v___x_157_);
v___x_160_ = lean_box(v___x_159_);
if (v_isShared_156_ == 0)
{
lean_ctor_set(v___x_155_, 0, v___x_160_);
v___x_162_ = v___x_155_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
v_a_165_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_152_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_152_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubInt___redArg___boxed(lean_object* v_e_173_, lean_object* v_a_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_e_173_, v_a_174_);
lean_dec(v_a_174_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubInt(lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_e_177_, v_a_179_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubInt___boxed(lean_object* v_e_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_Meta_Structural_isInstSubInt(v_e_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
lean_dec(v_a_188_);
lean_dec_ref(v_a_187_);
lean_dec(v_a_186_);
lean_dec_ref(v_a_185_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulInt___redArg(lean_object* v_e_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_195_, v_a_196_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_210_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_210_ == 0)
{
v___x_201_ = v___x_198_;
v_isShared_202_ = v_isSharedCheck_210_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_198_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_210_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_203_ = l_Lean_Expr_cleanupAnnotations(v_a_199_);
v___x_204_ = ((lean_object*)(l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1));
v___x_205_ = l_Lean_Expr_isConstOf(v___x_203_, v___x_204_);
lean_dec_ref(v___x_203_);
v___x_206_ = lean_box(v___x_205_);
if (v_isShared_202_ == 0)
{
lean_ctor_set(v___x_201_, 0, v___x_206_);
v___x_208_ = v___x_201_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v___x_206_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_a_211_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_198_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_198_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulInt___redArg___boxed(lean_object* v_e_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_e_219_, v_a_220_);
lean_dec(v_a_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulInt(lean_object* v_e_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_e_223_, v_a_225_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulInt___boxed(lean_object* v_e_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Meta_Structural_isInstMulInt(v_e_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivInt___redArg(lean_object* v_e_241_, lean_object* v_a_242_){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_241_, v_a_242_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_256_; 
v_a_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_256_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_256_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_256_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_249_ = l_Lean_Expr_cleanupAnnotations(v_a_245_);
v___x_250_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1));
v___x_251_ = l_Lean_Expr_isConstOf(v___x_249_, v___x_250_);
lean_dec_ref(v___x_249_);
v___x_252_ = lean_box(v___x_251_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 0, v___x_252_);
v___x_254_ = v___x_247_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_a_257_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_244_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_244_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivInt___redArg___boxed(lean_object* v_e_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Meta_Structural_isInstDivInt___redArg(v_e_265_, v_a_266_);
lean_dec(v_a_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivInt(lean_object* v_e_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_Structural_isInstDivInt___redArg(v_e_269_, v_a_271_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivInt___boxed(lean_object* v_e_276_, lean_object* v_a_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Meta_Structural_isInstDivInt(v_e_276_, v_a_277_, v_a_278_, v_a_279_, v_a_280_);
lean_dec(v_a_280_);
lean_dec_ref(v_a_279_);
lean_dec(v_a_278_);
lean_dec_ref(v_a_277_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModInt___redArg(lean_object* v_e_287_, lean_object* v_a_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_287_, v_a_288_);
if (lean_obj_tag(v___x_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_302_; 
v_a_291_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_302_ == 0)
{
v___x_293_ = v___x_290_;
v_isShared_294_ = v_isSharedCheck_302_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_302_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_295_ = l_Lean_Expr_cleanupAnnotations(v_a_291_);
v___x_296_ = ((lean_object*)(l_Lean_Meta_Structural_isInstModInt___redArg___closed__1));
v___x_297_ = l_Lean_Expr_isConstOf(v___x_295_, v___x_296_);
lean_dec_ref(v___x_295_);
v___x_298_ = lean_box(v___x_297_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_298_);
v___x_300_ = v___x_293_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_298_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
v_a_303_ = lean_ctor_get(v___x_290_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_290_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_290_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_290_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModInt___redArg___boxed(lean_object* v_e_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Meta_Structural_isInstModInt___redArg(v_e_311_, v_a_312_);
lean_dec(v_a_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModInt(lean_object* v_e_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_Structural_isInstModInt___redArg(v_e_315_, v_a_317_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModInt___boxed(lean_object* v_e_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Meta_Structural_isInstModInt(v_e_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg(lean_object* v_e_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_333_, v_a_334_);
if (lean_obj_tag(v___x_336_) == 0)
{
lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_348_; 
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_348_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_348_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_348_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_341_ = l_Lean_Expr_cleanupAnnotations(v_a_337_);
v___x_342_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1));
v___x_343_ = l_Lean_Expr_isConstOf(v___x_341_, v___x_342_);
lean_dec_ref(v___x_341_);
v___x_344_ = lean_box(v___x_343_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_344_);
v___x_346_ = v___x_339_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_a_349_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_336_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_336_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg___boxed(lean_object* v_e_357_, lean_object* v_a_358_, lean_object* v_a_359_){
_start:
{
lean_object* v_res_360_; 
v_res_360_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_e_357_, v_a_358_);
lean_dec(v_a_358_);
return v_res_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdInt(lean_object* v_e_361_, lean_object* v_a_362_, lean_object* v_a_363_, lean_object* v_a_364_, lean_object* v_a_365_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_e_361_, v_a_363_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdInt___boxed(lean_object* v_e_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Meta_Structural_isInstDvdInt(v_e_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object* v_e_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_378_, v_a_379_);
if (lean_obj_tag(v___x_381_) == 0)
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_401_; 
v_a_382_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_401_ == 0)
{
v___x_384_ = v___x_381_;
v_isShared_385_ = v_isSharedCheck_401_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_381_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_401_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = l_Lean_Expr_cleanupAnnotations(v_a_382_);
v___x_393_ = l_Lean_Expr_isApp(v___x_392_);
if (v___x_393_ == 0)
{
lean_dec_ref(v___x_392_);
goto v___jp_386_;
}
else
{
lean_object* v_arg_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_arg_394_ = lean_ctor_get(v___x_392_, 1);
lean_inc_ref(v_arg_394_);
v___x_395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_392_);
v___x_396_ = l_Lean_Expr_isApp(v___x_395_);
if (v___x_396_ == 0)
{
lean_dec_ref(v___x_395_);
lean_dec_ref(v_arg_394_);
goto v___jp_386_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_397_ = l_Lean_Expr_appFnCleanup___redArg(v___x_395_);
v___x_398_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__1));
v___x_399_ = l_Lean_Expr_isConstOf(v___x_397_, v___x_398_);
lean_dec_ref(v___x_397_);
if (v___x_399_ == 0)
{
lean_dec_ref(v_arg_394_);
goto v___jp_386_;
}
else
{
lean_object* v___x_400_; 
lean_del_object(v___x_384_);
v___x_400_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_arg_394_, v_a_379_);
return v___x_400_;
}
}
}
v___jp_386_:
{
uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_387_ = 0;
v___x_388_ = lean_box(v___x_387_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 0, v___x_388_);
v___x_390_ = v___x_384_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v___x_388_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_402_; lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_a_402_ = lean_ctor_get(v___x_381_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_381_);
if (v_isSharedCheck_409_ == 0)
{
v___x_404_ = v___x_381_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_inc(v_a_402_);
lean_dec(v___x_381_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_402_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg___boxed(lean_object* v_e_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_e_410_, v_a_411_);
lean_dec(v_a_411_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddInt(lean_object* v_e_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_e_414_, v_a_416_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddInt___boxed(lean_object* v_e_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_Structural_isInstHAddInt(v_e_421_, v_a_422_, v_a_423_, v_a_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
lean_dec(v_a_423_);
lean_dec_ref(v_a_422_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object* v_e_431_, lean_object* v_a_432_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_431_, v_a_432_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_454_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_454_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_454_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_454_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = l_Lean_Expr_cleanupAnnotations(v_a_435_);
v___x_446_ = l_Lean_Expr_isApp(v___x_445_);
if (v___x_446_ == 0)
{
lean_dec_ref(v___x_445_);
goto v___jp_439_;
}
else
{
lean_object* v_arg_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_arg_447_ = lean_ctor_get(v___x_445_, 1);
lean_inc_ref(v_arg_447_);
v___x_448_ = l_Lean_Expr_appFnCleanup___redArg(v___x_445_);
v___x_449_ = l_Lean_Expr_isApp(v___x_448_);
if (v___x_449_ == 0)
{
lean_dec_ref(v___x_448_);
lean_dec_ref(v_arg_447_);
goto v___jp_439_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_450_ = l_Lean_Expr_appFnCleanup___redArg(v___x_448_);
v___x_451_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__1));
v___x_452_ = l_Lean_Expr_isConstOf(v___x_450_, v___x_451_);
lean_dec_ref(v___x_450_);
if (v___x_452_ == 0)
{
lean_dec_ref(v_arg_447_);
goto v___jp_439_;
}
else
{
lean_object* v___x_453_; 
lean_del_object(v___x_437_);
v___x_453_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_arg_447_, v_a_432_);
return v___x_453_;
}
}
}
v___jp_439_:
{
uint8_t v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_440_ = 0;
v___x_441_ = lean_box(v___x_440_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 0, v___x_441_);
v___x_443_ = v___x_437_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_455_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_434_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_434_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg___boxed(lean_object* v_e_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_e_463_, v_a_464_);
lean_dec(v_a_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubInt(lean_object* v_e_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v___x_473_; 
v___x_473_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_e_467_, v_a_469_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubInt___boxed(lean_object* v_e_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_Structural_isInstHSubInt(v_e_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
lean_dec(v_a_478_);
lean_dec_ref(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object* v_e_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_484_, v_a_485_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_507_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_507_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_507_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_507_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_498_ = l_Lean_Expr_cleanupAnnotations(v_a_488_);
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
v___x_504_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__1));
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
lean_del_object(v___x_490_);
v___x_506_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_arg_500_, v_a_485_);
return v___x_506_;
}
}
}
v___jp_492_:
{
uint8_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_493_ = 0;
v___x_494_ = lean_box(v___x_493_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_494_);
v___x_496_ = v___x_490_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
v_a_508_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_487_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_487_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg___boxed(lean_object* v_e_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_e_516_, v_a_517_);
lean_dec(v_a_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulInt(lean_object* v_e_520_, lean_object* v_a_521_, lean_object* v_a_522_, lean_object* v_a_523_, lean_object* v_a_524_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_e_520_, v_a_522_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulInt___boxed(lean_object* v_e_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_Meta_Structural_isInstHMulInt(v_e_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg(lean_object* v_e_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_540_; 
v___x_540_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_537_, v_a_538_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_560_; 
v_a_541_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_560_ == 0)
{
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_560_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_540_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_560_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_551_ = l_Lean_Expr_cleanupAnnotations(v_a_541_);
v___x_552_ = l_Lean_Expr_isApp(v___x_551_);
if (v___x_552_ == 0)
{
lean_dec_ref(v___x_551_);
goto v___jp_545_;
}
else
{
lean_object* v_arg_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_arg_553_ = lean_ctor_get(v___x_551_, 1);
lean_inc_ref(v_arg_553_);
v___x_554_ = l_Lean_Expr_appFnCleanup___redArg(v___x_551_);
v___x_555_ = l_Lean_Expr_isApp(v___x_554_);
if (v___x_555_ == 0)
{
lean_dec_ref(v___x_554_);
lean_dec_ref(v_arg_553_);
goto v___jp_545_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_556_ = l_Lean_Expr_appFnCleanup___redArg(v___x_554_);
v___x_557_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__1));
v___x_558_ = l_Lean_Expr_isConstOf(v___x_556_, v___x_557_);
lean_dec_ref(v___x_556_);
if (v___x_558_ == 0)
{
lean_dec_ref(v_arg_553_);
goto v___jp_545_;
}
else
{
lean_object* v___x_559_; 
lean_del_object(v___x_543_);
v___x_559_ = l_Lean_Meta_Structural_isInstDivInt___redArg(v_arg_553_, v_a_538_);
return v___x_559_;
}
}
}
v___jp_545_:
{
uint8_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_546_ = 0;
v___x_547_ = lean_box(v___x_546_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 0, v___x_547_);
v___x_549_ = v___x_543_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_object* v_a_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_a_561_ = lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_540_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___x_540_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_a_561_);
lean_dec(v___x_540_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_a_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg___boxed(lean_object* v_e_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_e_569_, v_a_570_);
lean_dec(v_a_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivInt(lean_object* v_e_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_e_573_, v_a_575_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivInt___boxed(lean_object* v_e_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_Meta_Structural_isInstHDivInt(v_e_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_);
lean_dec(v_a_584_);
lean_dec_ref(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg(lean_object* v_e_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_590_, v_a_591_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_613_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_613_ == 0)
{
v___x_596_ = v___x_593_;
v_isShared_597_ = v_isSharedCheck_613_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_593_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_613_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = l_Lean_Expr_cleanupAnnotations(v_a_594_);
v___x_605_ = l_Lean_Expr_isApp(v___x_604_);
if (v___x_605_ == 0)
{
lean_dec_ref(v___x_604_);
goto v___jp_598_;
}
else
{
lean_object* v_arg_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_arg_606_ = lean_ctor_get(v___x_604_, 1);
lean_inc_ref(v_arg_606_);
v___x_607_ = l_Lean_Expr_appFnCleanup___redArg(v___x_604_);
v___x_608_ = l_Lean_Expr_isApp(v___x_607_);
if (v___x_608_ == 0)
{
lean_dec_ref(v___x_607_);
lean_dec_ref(v_arg_606_);
goto v___jp_598_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = l_Lean_Expr_appFnCleanup___redArg(v___x_607_);
v___x_610_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHModInt___redArg___closed__1));
v___x_611_ = l_Lean_Expr_isConstOf(v___x_609_, v___x_610_);
lean_dec_ref(v___x_609_);
if (v___x_611_ == 0)
{
lean_dec_ref(v_arg_606_);
goto v___jp_598_;
}
else
{
lean_object* v___x_612_; 
lean_del_object(v___x_596_);
v___x_612_ = l_Lean_Meta_Structural_isInstModInt___redArg(v_arg_606_, v_a_591_);
return v___x_612_;
}
}
}
v___jp_598_:
{
uint8_t v___x_599_; lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_599_ = 0;
v___x_600_ = lean_box(v___x_599_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 0, v___x_600_);
v___x_602_ = v___x_596_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
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
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
v_a_614_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_593_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_593_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg___boxed(lean_object* v_e_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_e_622_, v_a_623_);
lean_dec(v_a_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModInt(lean_object* v_e_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_e_626_, v_a_628_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModInt___boxed(lean_object* v_e_633_, lean_object* v_a_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_Meta_Structural_isInstHModInt(v_e_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_);
lean_dec(v_a_637_);
lean_dec_ref(v_a_636_);
lean_dec(v_a_635_);
lean_dec_ref(v_a_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTInt___redArg(lean_object* v_e_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_644_, v_a_645_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_659_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_659_ == 0)
{
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_659_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_659_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_652_ = l_Lean_Expr_cleanupAnnotations(v_a_648_);
v___x_653_ = ((lean_object*)(l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1));
v___x_654_ = l_Lean_Expr_isConstOf(v___x_652_, v___x_653_);
lean_dec_ref(v___x_652_);
v___x_655_ = lean_box(v___x_654_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_655_);
v___x_657_ = v___x_650_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
v_a_660_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_647_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_647_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTInt___redArg___boxed(lean_object* v_e_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lean_Meta_Structural_isInstLTInt___redArg(v_e_668_, v_a_669_);
lean_dec(v_a_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTInt(lean_object* v_e_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Lean_Meta_Structural_isInstLTInt___redArg(v_e_672_, v_a_674_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTInt___boxed(lean_object* v_e_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Meta_Structural_isInstLTInt(v_e_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg(lean_object* v_e_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_690_, v_a_691_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_705_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_705_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_698_ = l_Lean_Expr_cleanupAnnotations(v_a_694_);
v___x_699_ = ((lean_object*)(l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1));
v___x_700_ = l_Lean_Expr_isConstOf(v___x_698_, v___x_699_);
lean_dec_ref(v___x_698_);
v___x_701_ = lean_box(v___x_700_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_701_);
v___x_703_ = v___x_696_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
else
{
lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_706_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_713_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___x_693_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_dec(v___x_693_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg___boxed(lean_object* v_e_714_, lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_e_714_, v_a_715_);
lean_dec(v_a_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLEInt(lean_object* v_e_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_e_718_, v_a_720_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLEInt___boxed(lean_object* v_e_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Meta_Structural_isInstLEInt(v_e_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_);
lean_dec(v_a_729_);
lean_dec_ref(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowInt___redArg(lean_object* v_e_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_736_, v_a_737_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_751_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_751_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_751_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_751_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_744_ = l_Lean_Expr_cleanupAnnotations(v_a_740_);
v___x_745_ = ((lean_object*)(l_Lean_Meta_Structural_isInstNatPowInt___redArg___closed__1));
v___x_746_ = l_Lean_Expr_isConstOf(v___x_744_, v___x_745_);
lean_dec_ref(v___x_744_);
v___x_747_ = lean_box(v___x_746_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 0, v___x_747_);
v___x_749_ = v___x_742_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
v_a_752_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_739_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_739_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowInt___redArg___boxed(lean_object* v_e_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg(v_e_760_, v_a_761_);
lean_dec(v_a_761_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowInt(lean_object* v_e_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg(v_e_764_, v_a_766_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowInt___boxed(lean_object* v_e_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lean_Meta_Structural_isInstNatPowInt(v_e_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowInt___redArg(lean_object* v_e_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_781_, v_a_782_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_804_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_804_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_804_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_804_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_795_ = l_Lean_Expr_cleanupAnnotations(v_a_785_);
v___x_796_ = l_Lean_Expr_isApp(v___x_795_);
if (v___x_796_ == 0)
{
lean_dec_ref(v___x_795_);
goto v___jp_789_;
}
else
{
lean_object* v_arg_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_arg_797_ = lean_ctor_get(v___x_795_, 1);
lean_inc_ref(v_arg_797_);
v___x_798_ = l_Lean_Expr_appFnCleanup___redArg(v___x_795_);
v___x_799_ = l_Lean_Expr_isApp(v___x_798_);
if (v___x_799_ == 0)
{
lean_dec_ref(v___x_798_);
lean_dec_ref(v_arg_797_);
goto v___jp_789_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = l_Lean_Expr_appFnCleanup___redArg(v___x_798_);
v___x_801_ = ((lean_object*)(l_Lean_Meta_Structural_isInstPowInt___redArg___closed__1));
v___x_802_ = l_Lean_Expr_isConstOf(v___x_800_, v___x_801_);
lean_dec_ref(v___x_800_);
if (v___x_802_ == 0)
{
lean_dec_ref(v_arg_797_);
goto v___jp_789_;
}
else
{
lean_object* v___x_803_; 
lean_del_object(v___x_787_);
v___x_803_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg(v_arg_797_, v_a_782_);
return v___x_803_;
}
}
}
v___jp_789_:
{
uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_790_ = 0;
v___x_791_ = lean_box(v___x_790_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_791_);
v___x_793_ = v___x_787_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
v_a_805_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_784_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_784_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowInt___redArg___boxed(lean_object* v_e_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Meta_Structural_isInstPowInt___redArg(v_e_813_, v_a_814_);
lean_dec(v_a_814_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowInt(lean_object* v_e_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Meta_Structural_isInstPowInt___redArg(v_e_817_, v_a_819_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowInt___boxed(lean_object* v_e_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Meta_Structural_isInstPowInt(v_e_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg(lean_object* v_e_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_834_, v_a_835_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_840_; uint8_t v_isShared_841_; uint8_t v_isSharedCheck_859_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_859_ == 0)
{
v___x_840_ = v___x_837_;
v_isShared_841_ = v_isSharedCheck_859_;
goto v_resetjp_839_;
}
else
{
lean_inc(v_a_838_);
lean_dec(v___x_837_);
v___x_840_ = lean_box(0);
v_isShared_841_ = v_isSharedCheck_859_;
goto v_resetjp_839_;
}
v_resetjp_839_:
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = l_Lean_Expr_cleanupAnnotations(v_a_838_);
v___x_849_ = l_Lean_Expr_isApp(v___x_848_);
if (v___x_849_ == 0)
{
lean_dec_ref(v___x_848_);
goto v___jp_842_;
}
else
{
lean_object* v_arg_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_arg_850_ = lean_ctor_get(v___x_848_, 1);
lean_inc_ref(v_arg_850_);
v___x_851_ = l_Lean_Expr_appFnCleanup___redArg(v___x_848_);
v___x_852_ = l_Lean_Expr_isApp(v___x_851_);
if (v___x_852_ == 0)
{
lean_dec_ref(v___x_851_);
lean_dec_ref(v_arg_850_);
goto v___jp_842_;
}
else
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = l_Lean_Expr_appFnCleanup___redArg(v___x_851_);
v___x_854_ = l_Lean_Expr_isApp(v___x_853_);
if (v___x_854_ == 0)
{
lean_dec_ref(v___x_853_);
lean_dec_ref(v_arg_850_);
goto v___jp_842_;
}
else
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_855_ = l_Lean_Expr_appFnCleanup___redArg(v___x_853_);
v___x_856_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__1));
v___x_857_ = l_Lean_Expr_isConstOf(v___x_855_, v___x_856_);
lean_dec_ref(v___x_855_);
if (v___x_857_ == 0)
{
lean_dec_ref(v_arg_850_);
goto v___jp_842_;
}
else
{
lean_object* v___x_858_; 
lean_del_object(v___x_840_);
v___x_858_ = l_Lean_Meta_Structural_isInstPowInt___redArg(v_arg_850_, v_a_835_);
return v___x_858_;
}
}
}
}
v___jp_842_:
{
uint8_t v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_843_ = 0;
v___x_844_ = lean_box(v___x_843_);
if (v_isShared_841_ == 0)
{
lean_ctor_set(v___x_840_, 0, v___x_844_);
v___x_846_ = v___x_840_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_a_860_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_837_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_837_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg___boxed(lean_object* v_e_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_e_868_, v_a_869_);
lean_dec(v_a_869_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowInt(lean_object* v_e_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_e_872_, v_a_874_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowInt___boxed(lean_object* v_e_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Meta_Structural_isInstHPowInt(v_e_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstNegInt(lean_object* v_e_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_892_; 
lean_inc_ref(v_e_886_);
v___x_892_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_e_886_, v_a_888_);
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; uint8_t v___x_894_; 
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
v___x_894_ = lean_unbox(v_a_893_);
lean_dec(v_a_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref(v___x_892_);
v___x_895_ = l_Lean_Int_mkInstNeg;
v___x_896_ = l_Lean_Meta_isDefEqI(v_e_886_, v___x_895_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_896_;
}
else
{
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec_ref(v_e_886_);
return v___x_892_;
}
}
else
{
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec_ref(v_e_886_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstNegInt___boxed(lean_object* v_e_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_Meta_DefEq_isInstNegInt(v_e_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddInt(lean_object* v_e_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_910_; 
lean_inc_ref(v_e_904_);
v___x_910_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_e_904_, v_a_906_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; uint8_t v___x_912_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
v___x_912_ = lean_unbox(v_a_911_);
lean_dec(v_a_911_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec_ref(v___x_910_);
v___x_913_ = l_Lean_Int_mkInstAdd;
v___x_914_ = l_Lean_Meta_isDefEqI(v_e_904_, v___x_913_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v___x_914_;
}
else
{
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec_ref(v_e_904_);
return v___x_910_;
}
}
else
{
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
lean_dec(v_a_906_);
lean_dec_ref(v_a_905_);
lean_dec_ref(v_e_904_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddInt___boxed(lean_object* v_e_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Meta_DefEq_isInstAddInt(v_e_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddInt(lean_object* v_e_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; 
lean_inc_ref(v_e_922_);
v___x_928_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_e_922_, v_a_924_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v_a_929_; uint8_t v___x_930_; 
v_a_929_ = lean_ctor_get(v___x_928_, 0);
lean_inc(v_a_929_);
v___x_930_ = lean_unbox(v_a_929_);
lean_dec(v_a_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec_ref(v___x_928_);
v___x_931_ = l_Lean_Int_mkInstHAdd;
v___x_932_ = l_Lean_Meta_isDefEqI(v_e_922_, v___x_931_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
return v___x_932_;
}
else
{
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_e_922_);
return v___x_928_;
}
}
else
{
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_e_922_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddInt___boxed(lean_object* v_e_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_DefEq_isInstHAddInt(v_e_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstSubInt(lean_object* v_e_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; 
lean_inc_ref(v_e_940_);
v___x_946_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_e_940_, v_a_942_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; uint8_t v___x_948_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
v___x_948_ = lean_unbox(v_a_947_);
lean_dec(v_a_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec_ref(v___x_946_);
v___x_949_ = l_Lean_Int_mkInstSub;
v___x_950_ = l_Lean_Meta_isDefEqI(v_e_940_, v___x_949_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
return v___x_950_;
}
else
{
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec_ref(v_e_940_);
return v___x_946_;
}
}
else
{
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
lean_dec_ref(v_e_940_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstSubInt___boxed(lean_object* v_e_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_Meta_DefEq_isInstSubInt(v_e_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHSubInt(lean_object* v_e_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___x_964_; 
lean_inc_ref(v_e_958_);
v___x_964_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_e_958_, v_a_960_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_a_965_; uint8_t v___x_966_; 
v_a_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_a_965_);
v___x_966_ = lean_unbox(v_a_965_);
lean_dec(v_a_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec_ref(v___x_964_);
v___x_967_ = l_Lean_Int_mkInstHSub;
v___x_968_ = l_Lean_Meta_isDefEqI(v_e_958_, v___x_967_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
return v___x_968_;
}
else
{
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec_ref(v_e_958_);
return v___x_964_;
}
}
else
{
lean_dec(v_a_962_);
lean_dec_ref(v_a_961_);
lean_dec(v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec_ref(v_e_958_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHSubInt___boxed(lean_object* v_e_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_){
_start:
{
lean_object* v_res_975_; 
v_res_975_ = l_Lean_Meta_DefEq_isInstHSubInt(v_e_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulInt(lean_object* v_e_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_982_; 
lean_inc_ref(v_e_976_);
v___x_982_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_e_976_, v_a_978_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; uint8_t v___x_984_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
v___x_984_ = lean_unbox(v_a_983_);
lean_dec(v_a_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; 
lean_dec_ref(v___x_982_);
v___x_985_ = l_Lean_Int_mkInstMul;
v___x_986_ = l_Lean_Meta_isDefEqI(v_e_976_, v___x_985_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
return v___x_986_;
}
else
{
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec_ref(v_e_976_);
return v___x_982_;
}
}
else
{
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec_ref(v_e_976_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulInt___boxed(lean_object* v_e_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Meta_DefEq_isInstMulInt(v_e_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulInt(lean_object* v_e_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; 
lean_inc_ref(v_e_994_);
v___x_1000_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_e_994_, v_a_996_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; uint8_t v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
v___x_1002_ = lean_unbox(v_a_1001_);
lean_dec(v_a_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec_ref(v___x_1000_);
v___x_1003_ = l_Lean_Int_mkInstHMul;
v___x_1004_ = l_Lean_Meta_isDefEqI(v_e_994_, v___x_1003_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
return v___x_1004_;
}
else
{
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec_ref(v_e_994_);
return v___x_1000_;
}
}
else
{
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec_ref(v_e_994_);
return v___x_1000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulInt___boxed(lean_object* v_e_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Meta_DefEq_isInstHMulInt(v_e_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTInt(lean_object* v_e_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v___x_1018_; 
lean_inc_ref(v_e_1012_);
v___x_1018_ = l_Lean_Meta_Structural_isInstLTInt___redArg(v_e_1012_, v_a_1014_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v_a_1019_; uint8_t v___x_1020_; 
v_a_1019_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_a_1019_);
v___x_1020_ = lean_unbox(v_a_1019_);
lean_dec(v_a_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec_ref(v___x_1018_);
v___x_1021_ = l_Lean_Int_mkInstLT;
v___x_1022_ = l_Lean_Meta_isDefEqI(v_e_1012_, v___x_1021_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
return v___x_1022_;
}
else
{
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec_ref(v_e_1012_);
return v___x_1018_;
}
}
else
{
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec_ref(v_e_1012_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTInt___boxed(lean_object* v_e_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_Meta_DefEq_isInstLTInt(v_e_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLEInt(lean_object* v_e_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v___x_1036_; 
lean_inc_ref(v_e_1030_);
v___x_1036_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_e_1030_, v_a_1032_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v_a_1037_; uint8_t v___x_1038_; 
v_a_1037_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_a_1037_);
v___x_1038_ = lean_unbox(v_a_1037_);
lean_dec(v_a_1037_);
if (v___x_1038_ == 0)
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec_ref(v___x_1036_);
v___x_1039_ = l_Lean_Int_mkInstLE;
v___x_1040_ = l_Lean_Meta_isDefEqI(v_e_1030_, v___x_1039_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_);
return v___x_1040_;
}
else
{
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec_ref(v_e_1030_);
return v___x_1036_;
}
}
else
{
lean_dec(v_a_1034_);
lean_dec_ref(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec_ref(v_a_1031_);
lean_dec_ref(v_e_1030_);
return v___x_1036_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLEInt___boxed(lean_object* v_e_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Meta_DefEq_isInstLEInt(v_e_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
return v_res_1047_;
}
}
static lean_object* _init_l_Lean_Meta_DefEq_isInstDvdInt___closed__0(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1048_ = lean_box(0);
v___x_1049_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1));
v___x_1050_ = l_Lean_mkConst(v___x_1049_, v___x_1048_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstDvdInt(lean_object* v_e_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___x_1057_; 
lean_inc_ref(v_e_1051_);
v___x_1057_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_e_1051_, v_a_1053_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v_a_1058_; uint8_t v___x_1059_; 
v_a_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_a_1058_);
v___x_1059_ = lean_unbox(v_a_1058_);
lean_dec(v_a_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec_ref(v___x_1057_);
v___x_1060_ = lean_obj_once(&l_Lean_Meta_DefEq_isInstDvdInt___closed__0, &l_Lean_Meta_DefEq_isInstDvdInt___closed__0_once, _init_l_Lean_Meta_DefEq_isInstDvdInt___closed__0);
v___x_1061_ = l_Lean_Meta_isDefEqI(v_e_1051_, v___x_1060_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_);
return v___x_1061_;
}
else
{
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec_ref(v_e_1051_);
return v___x_1057_;
}
}
else
{
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec_ref(v_e_1051_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstDvdInt___boxed(lean_object* v_e_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Meta_DefEq_isInstDvdInt(v_e_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_);
return v_res_1068_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_IntInstTesters(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_IntInstTesters(builtin);
}
#ifdef __cplusplus
}
#endif
