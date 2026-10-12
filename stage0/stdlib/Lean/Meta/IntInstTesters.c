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
lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg(lean_object* v_e_4_, lean_object* v_a_5_){
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
v___x_19_ = ((lean_object*)(l_Lean_Meta_Structural_isInstOfNatInt___redArg___closed__1));
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
LEAN_EXPORT void l_Lean_Meta_Structural_isInstOfNatInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4_ = stack[0].m_obj;
lean_object* v_a_5_ = stack[1].m_obj;
lean_object* v_res_34_;
v_res_34_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v_e_4_, v_a_5_);
stack->m_obj
 = v_res_34_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatInt___redArg___boxed(lean_object* v_e_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v_e_35_, v_a_36_);
lean_dec(v_a_36_);
return v_res_38_;
}
}
lean_object* l_Lean_Meta_Structural_isInstOfNatInt(lean_object* v_e_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Meta_Structural_isInstOfNatInt___redArg(v_e_39_, v_a_41_);
return v___x_45_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstOfNatInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_39_ = stack[0].m_obj;
lean_object* v_a_40_ = stack[1].m_obj;
lean_object* v_a_41_ = stack[2].m_obj;
lean_object* v_a_42_ = stack[3].m_obj;
lean_object* v_a_43_ = stack[4].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lean_Meta_Structural_isInstOfNatInt(v_e_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstOfNatInt___boxed(lean_object* v_e_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_Structural_isInstOfNatInt(v_e_47_, v_a_48_, v_a_49_, v_a_50_, v_a_51_);
lean_dec(v_a_51_);
lean_dec_ref(v_a_50_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
return v_res_53_;
}
}
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object* v_e_59_, lean_object* v_a_60_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_59_, v_a_60_);
if (lean_obj_tag(v___x_62_) == 0)
{
lean_object* v_a_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_74_; 
v_a_63_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_74_ == 0)
{
v___x_65_ = v___x_62_;
v_isShared_66_ = v_isSharedCheck_74_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_a_63_);
lean_dec(v___x_62_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_74_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_67_ = l_Lean_Expr_cleanupAnnotations(v_a_63_);
v___x_68_ = ((lean_object*)(l_Lean_Meta_Structural_isInstNegInt___redArg___closed__2));
v___x_69_ = l_Lean_Expr_isConstOf(v___x_67_, v___x_68_);
lean_dec_ref(v___x_67_);
v___x_70_ = lean_box(v___x_69_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_70_);
v___x_72_ = v___x_65_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_73_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
return v___x_72_;
}
}
}
else
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_82_; 
v_a_75_ = lean_ctor_get(v___x_62_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_82_ == 0)
{
v___x_77_ = v___x_62_;
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_62_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_82_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
if (v_isShared_78_ == 0)
{
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v_a_75_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstNegInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_59_ = stack[0].m_obj;
lean_object* v_a_60_ = stack[1].m_obj;
lean_object* v_res_83_;
v_res_83_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_e_59_, v_a_60_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg___boxed(lean_object* v_e_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_e_84_, v_a_85_);
lean_dec(v_a_85_);
return v_res_87_;
}
}
lean_object* l_Lean_Meta_Structural_isInstNegInt(lean_object* v_e_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_e_88_, v_a_90_);
return v___x_94_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstNegInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_88_ = stack[0].m_obj;
lean_object* v_a_89_ = stack[1].m_obj;
lean_object* v_a_90_ = stack[2].m_obj;
lean_object* v_a_91_ = stack[3].m_obj;
lean_object* v_a_92_ = stack[4].m_obj;
lean_object* v_res_95_;
v_res_95_ = l_Lean_Meta_Structural_isInstNegInt(v_e_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
stack->m_obj
 = v_res_95_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNegInt___boxed(lean_object* v_e_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Meta_Structural_isInstNegInt(v_e_96_, v_a_97_, v_a_98_, v_a_99_, v_a_100_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
lean_dec(v_a_98_);
lean_dec_ref(v_a_97_);
return v_res_102_;
}
}
lean_object* l_Lean_Meta_Structural_isInstAddInt___redArg(lean_object* v_e_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_107_, v_a_108_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_122_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_122_ == 0)
{
v___x_113_ = v___x_110_;
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_a_111_);
lean_dec(v___x_110_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_122_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_120_; 
v___x_115_ = l_Lean_Expr_cleanupAnnotations(v_a_111_);
v___x_116_ = ((lean_object*)(l_Lean_Meta_Structural_isInstAddInt___redArg___closed__1));
v___x_117_ = l_Lean_Expr_isConstOf(v___x_115_, v___x_116_);
lean_dec_ref(v___x_115_);
v___x_118_ = lean_box(v___x_117_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_118_);
v___x_120_ = v___x_113_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_118_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
v_a_123_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v___x_110_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_110_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstAddInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_107_ = stack[0].m_obj;
lean_object* v_a_108_ = stack[1].m_obj;
lean_object* v_res_131_;
v_res_131_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_e_107_, v_a_108_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddInt___redArg___boxed(lean_object* v_e_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_e_132_, v_a_133_);
lean_dec(v_a_133_);
return v_res_135_;
}
}
lean_object* l_Lean_Meta_Structural_isInstAddInt(lean_object* v_e_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_e_136_, v_a_138_);
return v___x_142_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstAddInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_136_ = stack[0].m_obj;
lean_object* v_a_137_ = stack[1].m_obj;
lean_object* v_a_138_ = stack[2].m_obj;
lean_object* v_a_139_ = stack[3].m_obj;
lean_object* v_a_140_ = stack[4].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_Lean_Meta_Structural_isInstAddInt(v_e_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstAddInt___boxed(lean_object* v_e_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_Meta_Structural_isInstAddInt(v_e_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
return v_res_150_;
}
}
lean_object* l_Lean_Meta_Structural_isInstSubInt___redArg(lean_object* v_e_155_, lean_object* v_a_156_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_155_, v_a_156_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_170_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_170_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_170_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_170_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_163_ = l_Lean_Expr_cleanupAnnotations(v_a_159_);
v___x_164_ = ((lean_object*)(l_Lean_Meta_Structural_isInstSubInt___redArg___closed__1));
v___x_165_ = l_Lean_Expr_isConstOf(v___x_163_, v___x_164_);
lean_dec_ref(v___x_163_);
v___x_166_ = lean_box(v___x_165_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_166_);
v___x_168_ = v___x_161_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
else
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_158_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_158_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstSubInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_155_ = stack[0].m_obj;
lean_object* v_a_156_ = stack[1].m_obj;
lean_object* v_res_179_;
v_res_179_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_e_155_, v_a_156_);
stack->m_obj
 = v_res_179_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubInt___redArg___boxed(lean_object* v_e_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_e_180_, v_a_181_);
lean_dec(v_a_181_);
return v_res_183_;
}
}
lean_object* l_Lean_Meta_Structural_isInstSubInt(lean_object* v_e_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_e_184_, v_a_186_);
return v___x_190_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstSubInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_184_ = stack[0].m_obj;
lean_object* v_a_185_ = stack[1].m_obj;
lean_object* v_a_186_ = stack[2].m_obj;
lean_object* v_a_187_ = stack[3].m_obj;
lean_object* v_a_188_ = stack[4].m_obj;
lean_object* v_res_191_;
v_res_191_ = l_Lean_Meta_Structural_isInstSubInt(v_e_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_);
stack->m_obj
 = v_res_191_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstSubInt___boxed(lean_object* v_e_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Meta_Structural_isInstSubInt(v_e_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
return v_res_198_;
}
}
lean_object* l_Lean_Meta_Structural_isInstMulInt___redArg(lean_object* v_e_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_203_, v_a_204_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_218_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_218_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_218_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_211_ = l_Lean_Expr_cleanupAnnotations(v_a_207_);
v___x_212_ = ((lean_object*)(l_Lean_Meta_Structural_isInstMulInt___redArg___closed__1));
v___x_213_ = l_Lean_Expr_isConstOf(v___x_211_, v___x_212_);
lean_dec_ref(v___x_211_);
v___x_214_ = lean_box(v___x_213_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 0, v___x_214_);
v___x_216_ = v___x_209_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_214_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_226_; 
v_a_219_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_226_ == 0)
{
v___x_221_ = v___x_206_;
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_206_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_226_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_a_219_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstMulInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_203_ = stack[0].m_obj;
lean_object* v_a_204_ = stack[1].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_e_203_, v_a_204_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulInt___redArg___boxed(lean_object* v_e_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_e_228_, v_a_229_);
lean_dec(v_a_229_);
return v_res_231_;
}
}
lean_object* l_Lean_Meta_Structural_isInstMulInt(lean_object* v_e_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_e_232_, v_a_234_);
return v___x_238_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstMulInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_232_ = stack[0].m_obj;
lean_object* v_a_233_ = stack[1].m_obj;
lean_object* v_a_234_ = stack[2].m_obj;
lean_object* v_a_235_ = stack[3].m_obj;
lean_object* v_a_236_ = stack[4].m_obj;
lean_object* v_res_239_;
v_res_239_ = l_Lean_Meta_Structural_isInstMulInt(v_e_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
stack->m_obj
 = v_res_239_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstMulInt___boxed(lean_object* v_e_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_Structural_isInstMulInt(v_e_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
return v_res_246_;
}
}
lean_object* l_Lean_Meta_Structural_isInstDivInt___redArg(lean_object* v_e_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_251_, v_a_252_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_266_; 
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_266_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_266_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_266_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_259_; lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v___x_259_ = l_Lean_Expr_cleanupAnnotations(v_a_255_);
v___x_260_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDivInt___redArg___closed__1));
v___x_261_ = l_Lean_Expr_isConstOf(v___x_259_, v___x_260_);
lean_dec_ref(v___x_259_);
v___x_262_ = lean_box(v___x_261_);
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 0, v___x_262_);
v___x_264_ = v___x_257_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
v_a_267_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_254_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_254_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstDivInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_251_ = stack[0].m_obj;
lean_object* v_a_252_ = stack[1].m_obj;
lean_object* v_res_275_;
v_res_275_ = l_Lean_Meta_Structural_isInstDivInt___redArg(v_e_251_, v_a_252_);
stack->m_obj
 = v_res_275_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivInt___redArg___boxed(lean_object* v_e_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Meta_Structural_isInstDivInt___redArg(v_e_276_, v_a_277_);
lean_dec(v_a_277_);
return v_res_279_;
}
}
lean_object* l_Lean_Meta_Structural_isInstDivInt(lean_object* v_e_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Meta_Structural_isInstDivInt___redArg(v_e_280_, v_a_282_);
return v___x_286_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstDivInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_280_ = stack[0].m_obj;
lean_object* v_a_281_ = stack[1].m_obj;
lean_object* v_a_282_ = stack[2].m_obj;
lean_object* v_a_283_ = stack[3].m_obj;
lean_object* v_a_284_ = stack[4].m_obj;
lean_object* v_res_287_;
v_res_287_ = l_Lean_Meta_Structural_isInstDivInt(v_e_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDivInt___boxed(lean_object* v_e_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Meta_Structural_isInstDivInt(v_e_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_294_;
}
}
lean_object* l_Lean_Meta_Structural_isInstModInt___redArg(lean_object* v_e_299_, lean_object* v_a_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_299_, v_a_300_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_314_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_314_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_314_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_314_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_314_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_307_ = l_Lean_Expr_cleanupAnnotations(v_a_303_);
v___x_308_ = ((lean_object*)(l_Lean_Meta_Structural_isInstModInt___redArg___closed__1));
v___x_309_ = l_Lean_Expr_isConstOf(v___x_307_, v___x_308_);
lean_dec_ref(v___x_307_);
v___x_310_ = lean_box(v___x_309_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_310_);
v___x_312_ = v___x_305_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___x_310_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
v_a_315_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_302_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_302_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstModInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_299_ = stack[0].m_obj;
lean_object* v_a_300_ = stack[1].m_obj;
lean_object* v_res_323_;
v_res_323_ = l_Lean_Meta_Structural_isInstModInt___redArg(v_e_299_, v_a_300_);
stack->m_obj
 = v_res_323_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModInt___redArg___boxed(lean_object* v_e_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Meta_Structural_isInstModInt___redArg(v_e_324_, v_a_325_);
lean_dec(v_a_325_);
return v_res_327_;
}
}
lean_object* l_Lean_Meta_Structural_isInstModInt(lean_object* v_e_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_Meta_Structural_isInstModInt___redArg(v_e_328_, v_a_330_);
return v___x_334_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstModInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_328_ = stack[0].m_obj;
lean_object* v_a_329_ = stack[1].m_obj;
lean_object* v_a_330_ = stack[2].m_obj;
lean_object* v_a_331_ = stack[3].m_obj;
lean_object* v_a_332_ = stack[4].m_obj;
lean_object* v_res_335_;
v_res_335_ = l_Lean_Meta_Structural_isInstModInt(v_e_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_);
stack->m_obj
 = v_res_335_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstModInt___boxed(lean_object* v_e_336_, lean_object* v_a_337_, lean_object* v_a_338_, lean_object* v_a_339_, lean_object* v_a_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Meta_Structural_isInstModInt(v_e_336_, v_a_337_, v_a_338_, v_a_339_, v_a_340_);
lean_dec(v_a_340_);
lean_dec_ref(v_a_339_);
lean_dec(v_a_338_);
lean_dec_ref(v_a_337_);
return v_res_342_;
}
}
lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg(lean_object* v_e_347_, lean_object* v_a_348_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_347_, v_a_348_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_362_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_362_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_362_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_362_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_355_ = l_Lean_Expr_cleanupAnnotations(v_a_351_);
v___x_356_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1));
v___x_357_ = l_Lean_Expr_isConstOf(v___x_355_, v___x_356_);
lean_dec_ref(v___x_355_);
v___x_358_ = lean_box(v___x_357_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_358_);
v___x_360_ = v___x_353_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_a_363_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_350_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_350_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstDvdInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_347_ = stack[0].m_obj;
lean_object* v_a_348_ = stack[1].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_e_347_, v_a_348_);
stack->m_obj
 = v_res_371_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg___boxed(lean_object* v_e_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_e_372_, v_a_373_);
lean_dec(v_a_373_);
return v_res_375_;
}
}
lean_object* l_Lean_Meta_Structural_isInstDvdInt(lean_object* v_e_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_e_376_, v_a_378_);
return v___x_382_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstDvdInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_376_ = stack[0].m_obj;
lean_object* v_a_377_ = stack[1].m_obj;
lean_object* v_a_378_ = stack[2].m_obj;
lean_object* v_a_379_ = stack[3].m_obj;
lean_object* v_a_380_ = stack[4].m_obj;
lean_object* v_res_383_;
v_res_383_ = l_Lean_Meta_Structural_isInstDvdInt(v_e_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
stack->m_obj
 = v_res_383_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstDvdInt___boxed(lean_object* v_e_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Meta_Structural_isInstDvdInt(v_e_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_390_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object* v_e_394_, lean_object* v_a_395_){
_start:
{
lean_object* v___x_401_; 
v___x_401_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_394_, v_a_395_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v___x_401_, 1);
v___x_403_ = l_Lean_Expr_cleanupAnnotations(v_a_402_);
v___x_404_ = l_Lean_Expr_isApp(v___x_403_);
if (v___x_404_ == 0)
{
lean_dec_ref(v___x_403_);
goto v___jp_397_;
}
else
{
lean_object* v_arg_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_arg_405_ = lean_ctor_get(v___x_403_, 1);
lean_inc_ref(v_arg_405_);
v___x_406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_403_);
v___x_407_ = l_Lean_Expr_isApp(v___x_406_);
if (v___x_407_ == 0)
{
lean_dec_ref(v___x_406_);
lean_dec_ref(v_arg_405_);
goto v___jp_397_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = l_Lean_Expr_appFnCleanup___redArg(v___x_406_);
v___x_409_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHAddInt___redArg___closed__1));
v___x_410_ = l_Lean_Expr_isConstOf(v___x_408_, v___x_409_);
lean_dec_ref(v___x_408_);
if (v___x_410_ == 0)
{
lean_dec_ref(v_arg_405_);
goto v___jp_397_;
}
else
{
lean_object* v___x_411_; 
v___x_411_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_arg_405_, v_a_395_);
return v___x_411_;
}
}
}
}
else
{
lean_object* v_a_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_412_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_419_ == 0)
{
v___x_414_ = v___x_401_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_a_412_);
lean_dec(v___x_401_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_412_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
v___jp_397_:
{
uint8_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = 0;
v___x_399_ = lean_box(v___x_398_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHAddInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_394_ = stack[0].m_obj;
lean_object* v_a_395_ = stack[1].m_obj;
lean_object* v_res_420_;
v_res_420_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_e_394_, v_a_395_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg___boxed(lean_object* v_e_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_e_421_, v_a_422_);
lean_dec(v_a_422_);
return v_res_424_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHAddInt(lean_object* v_e_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_e_425_, v_a_427_);
return v___x_431_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHAddInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_425_ = stack[0].m_obj;
lean_object* v_a_426_ = stack[1].m_obj;
lean_object* v_a_427_ = stack[2].m_obj;
lean_object* v_a_428_ = stack[3].m_obj;
lean_object* v_a_429_ = stack[4].m_obj;
lean_object* v_res_432_;
v_res_432_ = l_Lean_Meta_Structural_isInstHAddInt(v_e_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
stack->m_obj
 = v_res_432_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHAddInt___boxed(lean_object* v_e_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_Structural_isInstHAddInt(v_e_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_439_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object* v_e_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_443_, v_a_444_);
if (lean_obj_tag(v___x_450_) == 0)
{
lean_object* v_a_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v_a_451_ = lean_ctor_get(v___x_450_, 0);
lean_inc(v_a_451_);
lean_dec_ref_known(v___x_450_, 1);
v___x_452_ = l_Lean_Expr_cleanupAnnotations(v_a_451_);
v___x_453_ = l_Lean_Expr_isApp(v___x_452_);
if (v___x_453_ == 0)
{
lean_dec_ref(v___x_452_);
goto v___jp_446_;
}
else
{
lean_object* v_arg_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v_arg_454_ = lean_ctor_get(v___x_452_, 1);
lean_inc_ref(v_arg_454_);
v___x_455_ = l_Lean_Expr_appFnCleanup___redArg(v___x_452_);
v___x_456_ = l_Lean_Expr_isApp(v___x_455_);
if (v___x_456_ == 0)
{
lean_dec_ref(v___x_455_);
lean_dec_ref(v_arg_454_);
goto v___jp_446_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_457_ = l_Lean_Expr_appFnCleanup___redArg(v___x_455_);
v___x_458_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHSubInt___redArg___closed__1));
v___x_459_ = l_Lean_Expr_isConstOf(v___x_457_, v___x_458_);
lean_dec_ref(v___x_457_);
if (v___x_459_ == 0)
{
lean_dec_ref(v_arg_454_);
goto v___jp_446_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_arg_454_, v_a_444_);
return v___x_460_;
}
}
}
}
else
{
lean_object* v_a_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_468_; 
v_a_461_ = lean_ctor_get(v___x_450_, 0);
v_isSharedCheck_468_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_468_ == 0)
{
v___x_463_ = v___x_450_;
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_a_461_);
lean_dec(v___x_450_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_468_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
lean_object* v___x_466_; 
if (v_isShared_464_ == 0)
{
v___x_466_ = v___x_463_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_a_461_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
}
v___jp_446_:
{
uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = 0;
v___x_448_ = lean_box(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHSubInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_443_ = stack[0].m_obj;
lean_object* v_a_444_ = stack[1].m_obj;
lean_object* v_res_469_;
v_res_469_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_e_443_, v_a_444_);
stack->m_obj
 = v_res_469_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg___boxed(lean_object* v_e_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_e_470_, v_a_471_);
lean_dec(v_a_471_);
return v_res_473_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHSubInt(lean_object* v_e_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_e_474_, v_a_476_);
return v___x_480_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHSubInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_474_ = stack[0].m_obj;
lean_object* v_a_475_ = stack[1].m_obj;
lean_object* v_a_476_ = stack[2].m_obj;
lean_object* v_a_477_ = stack[3].m_obj;
lean_object* v_a_478_ = stack[4].m_obj;
lean_object* v_res_481_;
v_res_481_ = l_Lean_Meta_Structural_isInstHSubInt(v_e_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_);
stack->m_obj
 = v_res_481_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHSubInt___boxed(lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Meta_Structural_isInstHSubInt(v_e_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
lean_dec(v_a_486_);
lean_dec_ref(v_a_485_);
lean_dec(v_a_484_);
lean_dec_ref(v_a_483_);
return v_res_488_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object* v_e_492_, lean_object* v_a_493_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_492_, v_a_493_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v___x_501_ = l_Lean_Expr_cleanupAnnotations(v_a_500_);
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
v___x_507_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHMulInt___redArg___closed__1));
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
v___x_509_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_arg_503_, v_a_493_);
return v___x_509_;
}
}
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
v_a_510_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_499_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_499_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
v___jp_495_:
{
uint8_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_496_ = 0;
v___x_497_ = lean_box(v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHMulInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_492_ = stack[0].m_obj;
lean_object* v_a_493_ = stack[1].m_obj;
lean_object* v_res_518_;
v_res_518_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_e_492_, v_a_493_);
stack->m_obj
 = v_res_518_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg___boxed(lean_object* v_e_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_e_519_, v_a_520_);
lean_dec(v_a_520_);
return v_res_522_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHMulInt(lean_object* v_e_523_, lean_object* v_a_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_e_523_, v_a_525_);
return v___x_529_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHMulInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_523_ = stack[0].m_obj;
lean_object* v_a_524_ = stack[1].m_obj;
lean_object* v_a_525_ = stack[2].m_obj;
lean_object* v_a_526_ = stack[3].m_obj;
lean_object* v_a_527_ = stack[4].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lean_Meta_Structural_isInstHMulInt(v_e_523_, v_a_524_, v_a_525_, v_a_526_, v_a_527_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHMulInt___boxed(lean_object* v_e_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Meta_Structural_isInstHMulInt(v_e_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
return v_res_537_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg(lean_object* v_e_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_541_, v_a_542_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_a_549_);
lean_dec_ref_known(v___x_548_, 1);
v___x_550_ = l_Lean_Expr_cleanupAnnotations(v_a_549_);
v___x_551_ = l_Lean_Expr_isApp(v___x_550_);
if (v___x_551_ == 0)
{
lean_dec_ref(v___x_550_);
goto v___jp_544_;
}
else
{
lean_object* v_arg_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_arg_552_ = lean_ctor_get(v___x_550_, 1);
lean_inc_ref(v_arg_552_);
v___x_553_ = l_Lean_Expr_appFnCleanup___redArg(v___x_550_);
v___x_554_ = l_Lean_Expr_isApp(v___x_553_);
if (v___x_554_ == 0)
{
lean_dec_ref(v___x_553_);
lean_dec_ref(v_arg_552_);
goto v___jp_544_;
}
else
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = l_Lean_Expr_appFnCleanup___redArg(v___x_553_);
v___x_556_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHDivInt___redArg___closed__1));
v___x_557_ = l_Lean_Expr_isConstOf(v___x_555_, v___x_556_);
lean_dec_ref(v___x_555_);
if (v___x_557_ == 0)
{
lean_dec_ref(v_arg_552_);
goto v___jp_544_;
}
else
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_Meta_Structural_isInstDivInt___redArg(v_arg_552_, v_a_542_);
return v___x_558_;
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_566_; 
v_a_559_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_566_ == 0)
{
v___x_561_ = v___x_548_;
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_548_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_566_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_a_559_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
v___jp_544_:
{
uint8_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_545_ = 0;
v___x_546_ = lean_box(v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHDivInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_541_ = stack[0].m_obj;
lean_object* v_a_542_ = stack[1].m_obj;
lean_object* v_res_567_;
v_res_567_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_e_541_, v_a_542_);
stack->m_obj
 = v_res_567_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg___boxed(lean_object* v_e_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_e_568_, v_a_569_);
lean_dec(v_a_569_);
return v_res_571_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHDivInt(lean_object* v_e_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Lean_Meta_Structural_isInstHDivInt___redArg(v_e_572_, v_a_574_);
return v___x_578_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHDivInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_572_ = stack[0].m_obj;
lean_object* v_a_573_ = stack[1].m_obj;
lean_object* v_a_574_ = stack[2].m_obj;
lean_object* v_a_575_ = stack[3].m_obj;
lean_object* v_a_576_ = stack[4].m_obj;
lean_object* v_res_579_;
v_res_579_ = l_Lean_Meta_Structural_isInstHDivInt(v_e_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
stack->m_obj
 = v_res_579_;
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
lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg(lean_object* v_e_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_590_, v_a_591_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = l_Lean_Expr_cleanupAnnotations(v_a_598_);
v___x_600_ = l_Lean_Expr_isApp(v___x_599_);
if (v___x_600_ == 0)
{
lean_dec_ref(v___x_599_);
goto v___jp_593_;
}
else
{
lean_object* v_arg_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v_arg_601_ = lean_ctor_get(v___x_599_, 1);
lean_inc_ref(v_arg_601_);
v___x_602_ = l_Lean_Expr_appFnCleanup___redArg(v___x_599_);
v___x_603_ = l_Lean_Expr_isApp(v___x_602_);
if (v___x_603_ == 0)
{
lean_dec_ref(v___x_602_);
lean_dec_ref(v_arg_601_);
goto v___jp_593_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_604_ = l_Lean_Expr_appFnCleanup___redArg(v___x_602_);
v___x_605_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHModInt___redArg___closed__1));
v___x_606_ = l_Lean_Expr_isConstOf(v___x_604_, v___x_605_);
lean_dec_ref(v___x_604_);
if (v___x_606_ == 0)
{
lean_dec_ref(v_arg_601_);
goto v___jp_593_;
}
else
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Meta_Structural_isInstModInt___redArg(v_arg_601_, v_a_591_);
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_615_; 
v_a_608_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_615_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_615_ == 0)
{
v___x_610_ = v___x_597_;
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_597_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_615_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_613_; 
if (v_isShared_611_ == 0)
{
v___x_613_ = v___x_610_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_a_608_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
v___jp_593_:
{
uint8_t v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_594_ = 0;
v___x_595_ = lean_box(v___x_594_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHModInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_590_ = stack[0].m_obj;
lean_object* v_a_591_ = stack[1].m_obj;
lean_object* v_res_616_;
v_res_616_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_e_590_, v_a_591_);
stack->m_obj
 = v_res_616_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg___boxed(lean_object* v_e_617_, lean_object* v_a_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_e_617_, v_a_618_);
lean_dec(v_a_618_);
return v_res_620_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHModInt(lean_object* v_e_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Meta_Structural_isInstHModInt___redArg(v_e_621_, v_a_623_);
return v___x_627_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHModInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_621_ = stack[0].m_obj;
lean_object* v_a_622_ = stack[1].m_obj;
lean_object* v_a_623_ = stack[2].m_obj;
lean_object* v_a_624_ = stack[3].m_obj;
lean_object* v_a_625_ = stack[4].m_obj;
lean_object* v_res_628_;
v_res_628_ = l_Lean_Meta_Structural_isInstHModInt(v_e_621_, v_a_622_, v_a_623_, v_a_624_, v_a_625_);
stack->m_obj
 = v_res_628_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHModInt___boxed(lean_object* v_e_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Meta_Structural_isInstHModInt(v_e_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_);
lean_dec(v_a_633_);
lean_dec_ref(v_a_632_);
lean_dec(v_a_631_);
lean_dec_ref(v_a_630_);
return v_res_635_;
}
}
lean_object* l_Lean_Meta_Structural_isInstLTInt___redArg(lean_object* v_e_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_640_, v_a_641_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_655_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_655_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_655_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_655_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_648_ = l_Lean_Expr_cleanupAnnotations(v_a_644_);
v___x_649_ = ((lean_object*)(l_Lean_Meta_Structural_isInstLTInt___redArg___closed__1));
v___x_650_ = l_Lean_Expr_isConstOf(v___x_648_, v___x_649_);
lean_dec_ref(v___x_648_);
v___x_651_ = lean_box(v___x_650_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_651_);
v___x_653_ = v___x_646_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
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
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstLTInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_640_ = stack[0].m_obj;
lean_object* v_a_641_ = stack[1].m_obj;
lean_object* v_res_664_;
v_res_664_ = l_Lean_Meta_Structural_isInstLTInt___redArg(v_e_640_, v_a_641_);
stack->m_obj
 = v_res_664_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTInt___redArg___boxed(lean_object* v_e_665_, lean_object* v_a_666_, lean_object* v_a_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Meta_Structural_isInstLTInt___redArg(v_e_665_, v_a_666_);
lean_dec(v_a_666_);
return v_res_668_;
}
}
lean_object* l_Lean_Meta_Structural_isInstLTInt(lean_object* v_e_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Meta_Structural_isInstLTInt___redArg(v_e_669_, v_a_671_);
return v___x_675_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstLTInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_669_ = stack[0].m_obj;
lean_object* v_a_670_ = stack[1].m_obj;
lean_object* v_a_671_ = stack[2].m_obj;
lean_object* v_a_672_ = stack[3].m_obj;
lean_object* v_a_673_ = stack[4].m_obj;
lean_object* v_res_676_;
v_res_676_ = l_Lean_Meta_Structural_isInstLTInt(v_e_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
stack->m_obj
 = v_res_676_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLTInt___boxed(lean_object* v_e_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_Meta_Structural_isInstLTInt(v_e_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
return v_res_683_;
}
}
lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg(lean_object* v_e_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_688_, v_a_689_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_703_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_703_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_703_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_703_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_696_ = l_Lean_Expr_cleanupAnnotations(v_a_692_);
v___x_697_ = ((lean_object*)(l_Lean_Meta_Structural_isInstLEInt___redArg___closed__1));
v___x_698_ = l_Lean_Expr_isConstOf(v___x_696_, v___x_697_);
lean_dec_ref(v___x_696_);
v___x_699_ = lean_box(v___x_698_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_699_);
v___x_701_ = v___x_694_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
v_a_704_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_691_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_691_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstLEInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_688_ = stack[0].m_obj;
lean_object* v_a_689_ = stack[1].m_obj;
lean_object* v_res_712_;
v_res_712_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_e_688_, v_a_689_);
stack->m_obj
 = v_res_712_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg___boxed(lean_object* v_e_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_e_713_, v_a_714_);
lean_dec(v_a_714_);
return v_res_716_;
}
}
lean_object* l_Lean_Meta_Structural_isInstLEInt(lean_object* v_e_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_e_717_, v_a_719_);
return v___x_723_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstLEInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_717_ = stack[0].m_obj;
lean_object* v_a_718_ = stack[1].m_obj;
lean_object* v_a_719_ = stack[2].m_obj;
lean_object* v_a_720_ = stack[3].m_obj;
lean_object* v_a_721_ = stack[4].m_obj;
lean_object* v_res_724_;
v_res_724_ = l_Lean_Meta_Structural_isInstLEInt(v_e_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
stack->m_obj
 = v_res_724_;
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
lean_object* l_Lean_Meta_Structural_isInstNatPowInt___redArg(lean_object* v_e_736_, lean_object* v_a_737_){
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
LEAN_EXPORT void l_Lean_Meta_Structural_isInstNatPowInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_736_ = stack[0].m_obj;
lean_object* v_a_737_ = stack[1].m_obj;
lean_object* v_res_760_;
v_res_760_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg(v_e_736_, v_a_737_);
stack->m_obj
 = v_res_760_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowInt___redArg___boxed(lean_object* v_e_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg(v_e_761_, v_a_762_);
lean_dec(v_a_762_);
return v_res_764_;
}
}
lean_object* l_Lean_Meta_Structural_isInstNatPowInt(lean_object* v_e_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg(v_e_765_, v_a_767_);
return v___x_771_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstNatPowInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_765_ = stack[0].m_obj;
lean_object* v_a_766_ = stack[1].m_obj;
lean_object* v_a_767_ = stack[2].m_obj;
lean_object* v_a_768_ = stack[3].m_obj;
lean_object* v_a_769_ = stack[4].m_obj;
lean_object* v_res_772_;
v_res_772_ = l_Lean_Meta_Structural_isInstNatPowInt(v_e_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_);
stack->m_obj
 = v_res_772_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstNatPowInt___boxed(lean_object* v_e_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Meta_Structural_isInstNatPowInt(v_e_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
return v_res_779_;
}
}
lean_object* l_Lean_Meta_Structural_isInstPowInt___redArg(lean_object* v_e_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_783_, v_a_784_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v___x_792_ = l_Lean_Expr_cleanupAnnotations(v_a_791_);
v___x_793_ = l_Lean_Expr_isApp(v___x_792_);
if (v___x_793_ == 0)
{
lean_dec_ref(v___x_792_);
goto v___jp_786_;
}
else
{
lean_object* v_arg_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_arg_794_ = lean_ctor_get(v___x_792_, 1);
lean_inc_ref(v_arg_794_);
v___x_795_ = l_Lean_Expr_appFnCleanup___redArg(v___x_792_);
v___x_796_ = l_Lean_Expr_isApp(v___x_795_);
if (v___x_796_ == 0)
{
lean_dec_ref(v___x_795_);
lean_dec_ref(v_arg_794_);
goto v___jp_786_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_797_ = l_Lean_Expr_appFnCleanup___redArg(v___x_795_);
v___x_798_ = ((lean_object*)(l_Lean_Meta_Structural_isInstPowInt___redArg___closed__1));
v___x_799_ = l_Lean_Expr_isConstOf(v___x_797_, v___x_798_);
lean_dec_ref(v___x_797_);
if (v___x_799_ == 0)
{
lean_dec_ref(v_arg_794_);
goto v___jp_786_;
}
else
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_Structural_isInstNatPowInt___redArg(v_arg_794_, v_a_784_);
return v___x_800_;
}
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v_a_801_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_790_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_790_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
v___jp_786_:
{
uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = 0;
v___x_788_ = lean_box(v___x_787_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v___x_788_);
return v___x_789_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstPowInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_783_ = stack[0].m_obj;
lean_object* v_a_784_ = stack[1].m_obj;
lean_object* v_res_809_;
v_res_809_ = l_Lean_Meta_Structural_isInstPowInt___redArg(v_e_783_, v_a_784_);
stack->m_obj
 = v_res_809_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowInt___redArg___boxed(lean_object* v_e_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Meta_Structural_isInstPowInt___redArg(v_e_810_, v_a_811_);
lean_dec(v_a_811_);
return v_res_813_;
}
}
lean_object* l_Lean_Meta_Structural_isInstPowInt(lean_object* v_e_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_Meta_Structural_isInstPowInt___redArg(v_e_814_, v_a_816_);
return v___x_820_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstPowInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_814_ = stack[0].m_obj;
lean_object* v_a_815_ = stack[1].m_obj;
lean_object* v_a_816_ = stack[2].m_obj;
lean_object* v_a_817_ = stack[3].m_obj;
lean_object* v_a_818_ = stack[4].m_obj;
lean_object* v_res_821_;
v_res_821_ = l_Lean_Meta_Structural_isInstPowInt(v_e_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
stack->m_obj
 = v_res_821_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstPowInt___boxed(lean_object* v_e_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Meta_Structural_isInstPowInt(v_e_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec_ref(v_a_825_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
return v_res_828_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg(lean_object* v_e_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_832_, v_a_833_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
v___x_841_ = l_Lean_Expr_cleanupAnnotations(v_a_840_);
v___x_842_ = l_Lean_Expr_isApp(v___x_841_);
if (v___x_842_ == 0)
{
lean_dec_ref(v___x_841_);
goto v___jp_835_;
}
else
{
lean_object* v_arg_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_arg_843_ = lean_ctor_get(v___x_841_, 1);
lean_inc_ref(v_arg_843_);
v___x_844_ = l_Lean_Expr_appFnCleanup___redArg(v___x_841_);
v___x_845_ = l_Lean_Expr_isApp(v___x_844_);
if (v___x_845_ == 0)
{
lean_dec_ref(v___x_844_);
lean_dec_ref(v_arg_843_);
goto v___jp_835_;
}
else
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = l_Lean_Expr_appFnCleanup___redArg(v___x_844_);
v___x_847_ = l_Lean_Expr_isApp(v___x_846_);
if (v___x_847_ == 0)
{
lean_dec_ref(v___x_846_);
lean_dec_ref(v_arg_843_);
goto v___jp_835_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_848_ = l_Lean_Expr_appFnCleanup___redArg(v___x_846_);
v___x_849_ = ((lean_object*)(l_Lean_Meta_Structural_isInstHPowInt___redArg___closed__1));
v___x_850_ = l_Lean_Expr_isConstOf(v___x_848_, v___x_849_);
lean_dec_ref(v___x_848_);
if (v___x_850_ == 0)
{
lean_dec_ref(v_arg_843_);
goto v___jp_835_;
}
else
{
lean_object* v___x_851_; 
v___x_851_ = l_Lean_Meta_Structural_isInstPowInt___redArg(v_arg_843_, v_a_833_);
return v___x_851_;
}
}
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_852_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_839_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_839_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
v___jp_835_:
{
uint8_t v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_836_ = 0;
v___x_837_ = lean_box(v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHPowInt___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_832_ = stack[0].m_obj;
lean_object* v_a_833_ = stack[1].m_obj;
lean_object* v_res_860_;
v_res_860_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_e_832_, v_a_833_);
stack->m_obj
 = v_res_860_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg___boxed(lean_object* v_e_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v_res_864_; 
v_res_864_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_e_861_, v_a_862_);
lean_dec(v_a_862_);
return v_res_864_;
}
}
lean_object* l_Lean_Meta_Structural_isInstHPowInt(lean_object* v_e_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_Meta_Structural_isInstHPowInt___redArg(v_e_865_, v_a_867_);
return v___x_871_;
}
}
LEAN_EXPORT void l_Lean_Meta_Structural_isInstHPowInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_865_ = stack[0].m_obj;
lean_object* v_a_866_ = stack[1].m_obj;
lean_object* v_a_867_ = stack[2].m_obj;
lean_object* v_a_868_ = stack[3].m_obj;
lean_object* v_a_869_ = stack[4].m_obj;
lean_object* v_res_872_;
v_res_872_ = l_Lean_Meta_Structural_isInstHPowInt(v_e_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
stack->m_obj
 = v_res_872_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Structural_isInstHPowInt___boxed(lean_object* v_e_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Meta_Structural_isInstHPowInt(v_e_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
return v_res_879_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstNegInt(lean_object* v_e_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; 
lean_inc_ref(v_e_880_);
v___x_886_ = l_Lean_Meta_Structural_isInstNegInt___redArg(v_e_880_, v_a_882_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; uint8_t v___x_888_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v___x_888_ = lean_unbox(v_a_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec_ref_known(v___x_886_, 1);
v___x_889_ = l_Lean_Int_mkInstNeg;
v___x_890_ = l_Lean_Meta_isDefEqI(v_e_880_, v___x_889_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
return v___x_890_;
}
else
{
lean_dec_ref(v_e_880_);
return v___x_886_;
}
}
else
{
lean_dec_ref(v_e_880_);
return v___x_886_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstNegInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_880_ = stack[0].m_obj;
lean_object* v_a_881_ = stack[1].m_obj;
lean_object* v_a_882_ = stack[2].m_obj;
lean_object* v_a_883_ = stack[3].m_obj;
lean_object* v_a_884_ = stack[4].m_obj;
lean_object* v_res_891_;
v_res_891_ = l_Lean_Meta_DefEq_isInstNegInt(v_e_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstNegInt___boxed(lean_object* v_e_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Meta_DefEq_isInstNegInt(v_e_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
return v_res_898_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstAddInt(lean_object* v_e_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_905_; 
lean_inc_ref(v_e_899_);
v___x_905_ = l_Lean_Meta_Structural_isInstAddInt___redArg(v_e_899_, v_a_901_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; uint8_t v___x_907_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
v___x_907_ = lean_unbox(v_a_906_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec_ref_known(v___x_905_, 1);
v___x_908_ = l_Lean_Int_mkInstAdd;
v___x_909_ = l_Lean_Meta_isDefEqI(v_e_899_, v___x_908_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
return v___x_909_;
}
else
{
lean_dec_ref(v_e_899_);
return v___x_905_;
}
}
else
{
lean_dec_ref(v_e_899_);
return v___x_905_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstAddInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_899_ = stack[0].m_obj;
lean_object* v_a_900_ = stack[1].m_obj;
lean_object* v_a_901_ = stack[2].m_obj;
lean_object* v_a_902_ = stack[3].m_obj;
lean_object* v_a_903_ = stack[4].m_obj;
lean_object* v_res_910_;
v_res_910_ = l_Lean_Meta_DefEq_isInstAddInt(v_e_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstAddInt___boxed(lean_object* v_e_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_Meta_DefEq_isInstAddInt(v_e_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
return v_res_917_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstHAddInt(lean_object* v_e_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_924_; 
lean_inc_ref(v_e_918_);
v___x_924_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_e_918_, v_a_920_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; uint8_t v___x_926_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v___x_926_ = lean_unbox(v_a_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_dec_ref_known(v___x_924_, 1);
v___x_927_ = l_Lean_Int_mkInstHAdd;
v___x_928_ = l_Lean_Meta_isDefEqI(v_e_918_, v___x_927_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
return v___x_928_;
}
else
{
lean_dec_ref(v_e_918_);
return v___x_924_;
}
}
else
{
lean_dec_ref(v_e_918_);
return v___x_924_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstHAddInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_918_ = stack[0].m_obj;
lean_object* v_a_919_ = stack[1].m_obj;
lean_object* v_a_920_ = stack[2].m_obj;
lean_object* v_a_921_ = stack[3].m_obj;
lean_object* v_a_922_ = stack[4].m_obj;
lean_object* v_res_929_;
v_res_929_ = l_Lean_Meta_DefEq_isInstHAddInt(v_e_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_);
stack->m_obj
 = v_res_929_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHAddInt___boxed(lean_object* v_e_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Meta_DefEq_isInstHAddInt(v_e_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_);
lean_dec(v_a_934_);
lean_dec_ref(v_a_933_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_936_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstSubInt(lean_object* v_e_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___x_943_; 
lean_inc_ref(v_e_937_);
v___x_943_ = l_Lean_Meta_Structural_isInstSubInt___redArg(v_e_937_, v_a_939_);
if (lean_obj_tag(v___x_943_) == 0)
{
lean_object* v_a_944_; uint8_t v___x_945_; 
v_a_944_ = lean_ctor_get(v___x_943_, 0);
v___x_945_ = lean_unbox(v_a_944_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_dec_ref_known(v___x_943_, 1);
v___x_946_ = l_Lean_Int_mkInstSub;
v___x_947_ = l_Lean_Meta_isDefEqI(v_e_937_, v___x_946_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
return v___x_947_;
}
else
{
lean_dec_ref(v_e_937_);
return v___x_943_;
}
}
else
{
lean_dec_ref(v_e_937_);
return v___x_943_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstSubInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_937_ = stack[0].m_obj;
lean_object* v_a_938_ = stack[1].m_obj;
lean_object* v_a_939_ = stack[2].m_obj;
lean_object* v_a_940_ = stack[3].m_obj;
lean_object* v_a_941_ = stack[4].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lean_Meta_DefEq_isInstSubInt(v_e_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstSubInt___boxed(lean_object* v_e_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Meta_DefEq_isInstSubInt(v_e_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
return v_res_955_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstHSubInt(lean_object* v_e_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v___x_962_; 
lean_inc_ref(v_e_956_);
v___x_962_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_e_956_, v_a_958_);
if (lean_obj_tag(v___x_962_) == 0)
{
lean_object* v_a_963_; uint8_t v___x_964_; 
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v___x_964_ = lean_unbox(v_a_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; 
lean_dec_ref_known(v___x_962_, 1);
v___x_965_ = l_Lean_Int_mkInstHSub;
v___x_966_ = l_Lean_Meta_isDefEqI(v_e_956_, v___x_965_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
return v___x_966_;
}
else
{
lean_dec_ref(v_e_956_);
return v___x_962_;
}
}
else
{
lean_dec_ref(v_e_956_);
return v___x_962_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstHSubInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_956_ = stack[0].m_obj;
lean_object* v_a_957_ = stack[1].m_obj;
lean_object* v_a_958_ = stack[2].m_obj;
lean_object* v_a_959_ = stack[3].m_obj;
lean_object* v_a_960_ = stack[4].m_obj;
lean_object* v_res_967_;
v_res_967_ = l_Lean_Meta_DefEq_isInstHSubInt(v_e_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
stack->m_obj
 = v_res_967_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHSubInt___boxed(lean_object* v_e_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Meta_DefEq_isInstHSubInt(v_e_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_974_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstMulInt(lean_object* v_e_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v___x_981_; 
lean_inc_ref(v_e_975_);
v___x_981_ = l_Lean_Meta_Structural_isInstMulInt___redArg(v_e_975_, v_a_977_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; uint8_t v___x_983_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
v___x_983_ = lean_unbox(v_a_982_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec_ref_known(v___x_981_, 1);
v___x_984_ = l_Lean_Int_mkInstMul;
v___x_985_ = l_Lean_Meta_isDefEqI(v_e_975_, v___x_984_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v___x_985_;
}
else
{
lean_dec_ref(v_e_975_);
return v___x_981_;
}
}
else
{
lean_dec_ref(v_e_975_);
return v___x_981_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstMulInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_975_ = stack[0].m_obj;
lean_object* v_a_976_ = stack[1].m_obj;
lean_object* v_a_977_ = stack[2].m_obj;
lean_object* v_a_978_ = stack[3].m_obj;
lean_object* v_a_979_ = stack[4].m_obj;
lean_object* v_res_986_;
v_res_986_ = l_Lean_Meta_DefEq_isInstMulInt(v_e_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
stack->m_obj
 = v_res_986_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstMulInt___boxed(lean_object* v_e_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_Meta_DefEq_isInstMulInt(v_e_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
lean_dec(v_a_991_);
lean_dec_ref(v_a_990_);
lean_dec(v_a_989_);
lean_dec_ref(v_a_988_);
return v_res_993_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstHMulInt(lean_object* v_e_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_1000_; 
lean_inc_ref(v_e_994_);
v___x_1000_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_e_994_, v_a_996_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; uint8_t v___x_1002_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v___x_1002_ = lean_unbox(v_a_1001_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec_ref_known(v___x_1000_, 1);
v___x_1003_ = l_Lean_Int_mkInstHMul;
v___x_1004_ = l_Lean_Meta_isDefEqI(v_e_994_, v___x_1003_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
return v___x_1004_;
}
else
{
lean_dec_ref(v_e_994_);
return v___x_1000_;
}
}
else
{
lean_dec_ref(v_e_994_);
return v___x_1000_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstHMulInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_994_ = stack[0].m_obj;
lean_object* v_a_995_ = stack[1].m_obj;
lean_object* v_a_996_ = stack[2].m_obj;
lean_object* v_a_997_ = stack[3].m_obj;
lean_object* v_a_998_ = stack[4].m_obj;
lean_object* v_res_1005_;
v_res_1005_ = l_Lean_Meta_DefEq_isInstHMulInt(v_e_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
stack->m_obj
 = v_res_1005_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstHMulInt___boxed(lean_object* v_e_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Meta_DefEq_isInstHMulInt(v_e_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_);
lean_dec(v_a_1010_);
lean_dec_ref(v_a_1009_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
return v_res_1012_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstLTInt(lean_object* v_e_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; 
lean_inc_ref(v_e_1013_);
v___x_1019_ = l_Lean_Meta_Structural_isInstLTInt___redArg(v_e_1013_, v_a_1015_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; uint8_t v___x_1021_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v___x_1021_ = lean_unbox(v_a_1020_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
lean_dec_ref_known(v___x_1019_, 1);
v___x_1022_ = l_Lean_Int_mkInstLT;
v___x_1023_ = l_Lean_Meta_isDefEqI(v_e_1013_, v___x_1022_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
return v___x_1023_;
}
else
{
lean_dec_ref(v_e_1013_);
return v___x_1019_;
}
}
else
{
lean_dec_ref(v_e_1013_);
return v___x_1019_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstLTInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1013_ = stack[0].m_obj;
lean_object* v_a_1014_ = stack[1].m_obj;
lean_object* v_a_1015_ = stack[2].m_obj;
lean_object* v_a_1016_ = stack[3].m_obj;
lean_object* v_a_1017_ = stack[4].m_obj;
lean_object* v_res_1024_;
v_res_1024_ = l_Lean_Meta_DefEq_isInstLTInt(v_e_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
stack->m_obj
 = v_res_1024_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLTInt___boxed(lean_object* v_e_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_Meta_DefEq_isInstLTInt(v_e_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_);
lean_dec(v_a_1029_);
lean_dec_ref(v_a_1028_);
lean_dec(v_a_1027_);
lean_dec_ref(v_a_1026_);
return v_res_1031_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstLEInt(lean_object* v_e_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v___x_1038_; 
lean_inc_ref(v_e_1032_);
v___x_1038_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_e_1032_, v_a_1034_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; uint8_t v___x_1040_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
v___x_1040_ = lean_unbox(v_a_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec_ref_known(v___x_1038_, 1);
v___x_1041_ = l_Lean_Int_mkInstLE;
v___x_1042_ = l_Lean_Meta_isDefEqI(v_e_1032_, v___x_1041_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
return v___x_1042_;
}
else
{
lean_dec_ref(v_e_1032_);
return v___x_1038_;
}
}
else
{
lean_dec_ref(v_e_1032_);
return v___x_1038_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstLEInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1032_ = stack[0].m_obj;
lean_object* v_a_1033_ = stack[1].m_obj;
lean_object* v_a_1034_ = stack[2].m_obj;
lean_object* v_a_1035_ = stack[3].m_obj;
lean_object* v_a_1036_ = stack[4].m_obj;
lean_object* v_res_1043_;
v_res_1043_ = l_Lean_Meta_DefEq_isInstLEInt(v_e_1032_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_);
stack->m_obj
 = v_res_1043_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstLEInt___boxed(lean_object* v_e_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_Meta_DefEq_isInstLEInt(v_e_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec_ref(v_a_1045_);
return v_res_1050_;
}
}
static lean_object* _init_l_Lean_Meta_DefEq_isInstDvdInt___closed__0(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = lean_box(0);
v___x_1052_ = ((lean_object*)(l_Lean_Meta_Structural_isInstDvdInt___redArg___closed__1));
v___x_1053_ = l_Lean_mkConst(v___x_1052_, v___x_1051_);
return v___x_1053_;
}
}
lean_object* l_Lean_Meta_DefEq_isInstDvdInt(lean_object* v_e_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v___x_1060_; 
lean_inc_ref(v_e_1054_);
v___x_1060_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_e_1054_, v_a_1056_);
if (lean_obj_tag(v___x_1060_) == 0)
{
lean_object* v_a_1061_; uint8_t v___x_1062_; 
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v___x_1062_ = lean_unbox(v_a_1061_);
if (v___x_1062_ == 0)
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec_ref_known(v___x_1060_, 1);
v___x_1063_ = lean_obj_once(&l_Lean_Meta_DefEq_isInstDvdInt___closed__0, &l_Lean_Meta_DefEq_isInstDvdInt___closed__0_once, _init_l_Lean_Meta_DefEq_isInstDvdInt___closed__0);
v___x_1064_ = l_Lean_Meta_isDefEqI(v_e_1054_, v___x_1063_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
return v___x_1064_;
}
else
{
lean_dec_ref(v_e_1054_);
return v___x_1060_;
}
}
else
{
lean_dec_ref(v_e_1054_);
return v___x_1060_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_DefEq_isInstDvdInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1054_ = stack[0].m_obj;
lean_object* v_a_1055_ = stack[1].m_obj;
lean_object* v_a_1056_ = stack[2].m_obj;
lean_object* v_a_1057_ = stack[3].m_obj;
lean_object* v_a_1058_ = stack[4].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_Lean_Meta_DefEq_isInstDvdInt(v_e_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_DefEq_isInstDvdInt___boxed(lean_object* v_e_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Meta_DefEq_isInstDvdInt(v_e_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
return v_res_1072_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_IntInstTesters(uint8_t builtin) {
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
